/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators

/-!
# Finite two-uniform Ramsey theorem

For `r ≥ 1` colors and every `k`, there is an `N` such that every coloring of
the 2-subsets of `Fin N` admits a monochromatic size-`k` set. This complements
`MathlibExt/Combinatorics/SimpleGraph/Ramsey.lean`, which covers the classical
graph (two-color, clique/independent-set) formulation; here the colors are
arbitrary (`Fin r`) and homogeneity is stated for set systems via
`Finset.powersetCard`.

Source: F. P. Ramsey, “On a Problem of Formal Logic,” Proceedings of the London
Mathematical Society s2-30 (1930), 264–286, DOI 10.1112/PLMS/S2-30.1.264.

Proof route: strong induction on the rank `∑ i, u i` of a target-size vector
`u : Fin r → ℕ`. If some target is `0`, `N = 0` works vacuously. Otherwise pick
a vertex `v`, pigeonhole the `N - 1` pairs through `v` into a large color fiber
`X`, pull the coloring back along the order embedding of a large finite subset
of `X`, apply the induction hypothesis to the decremented vector, and either
reattach `v` (same color) or keep the set found (different color).
-/

namespace MathlibExt.Combinatorics.Ramsey

private theorem sum_update_decr {r : ℕ} (t : Fin r → ℕ) (i₀ : Fin r)
    (hpos : 1 ≤ t i₀) :
    (∑ i, Function.update t i₀ (t i₀ - 1) i) + 1 = ∑ i, t i := by
  classical
  have hmem : i₀ ∈ (Finset.univ : Finset (Fin r)) := Finset.mem_univ i₀
  have h1 : t i₀ + ∑ x ∈ (Finset.univ.erase i₀ : Finset (Fin r)), t x =
      ∑ x ∈ (Finset.univ : Finset (Fin r)), t x :=
    Finset.add_sum_erase Finset.univ t hmem
  have h2 : Function.update t i₀ (t i₀ - 1) i₀ +
      ∑ x ∈ (Finset.univ.erase i₀ : Finset (Fin r)), Function.update t i₀ (t i₀ - 1) x =
      ∑ x ∈ (Finset.univ : Finset (Fin r)), Function.update t i₀ (t i₀ - 1) x :=
    Finset.add_sum_erase Finset.univ _ hmem
  have herase : ∑ x ∈ (Finset.univ.erase i₀ : Finset (Fin r)), Function.update t i₀ (t i₀ - 1) x =
      ∑ x ∈ (Finset.univ.erase i₀ : Finset (Fin r)), t x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ i₀ := (Finset.mem_erase.mp hx).1
    exact Function.update_of_ne hne _ _
  have hself : Function.update t i₀ (t i₀ - 1) i₀ = t i₀ - 1 :=
    Function.update_self i₀ _ _
  omega

private theorem exists_large_fiber {r : ℕ} (hr : 0 < r)
    (c n : Fin r → ℕ) (hsum : ∑ i, c i = ∑ i, n i) :
    ∃ i, n i ≤ c i := by
  by_contra h
  have hlt : ∀ i, c i < n i := by
    intro i
    by_contra hcon
    exact h ⟨i, by omega⟩
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin r)), c i + 1 ≤ n i := by
    intro i _
    have hi := hlt i
    omega
  have hsumle : ∑ i, (c i + 1) ≤ ∑ i, n i :=
    Finset.sum_le_sum hle
  have hadd : ∑ i, (c i + 1) = ∑ i, c i + r := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Nat.mul_one]
  omega

private theorem fiber_card_sum {N r : ℕ} (v : Fin N) (φ : Finset (Fin N) → Fin r) :
    (∑ i, (((Finset.univ.erase v).filter (fun w => φ {v, w} = i)).card)) =
      (Finset.univ.erase v).card := by
  have h : Set.MapsTo (fun w : Fin N => φ {v, w}) ↑(Finset.univ.erase v)
      ↑(Finset.univ : Finset (Fin r)) := by
    intro w hw
    exact Finset.mem_univ _
  have hh := Finset.card_eq_sum_card_fiberwise (f := (fun w : Fin N => φ {v, w}))
    (s := Finset.univ.erase v) (t := Finset.univ) h
  simpa using hh.symm

private theorem erase_card_eq {N : ℕ} (v : Fin N) :
    (Finset.univ.erase v).card = N - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]

private theorem exists_map_preimage_powersetCard {α β : Type*}
    (e : α ↪ β) (S' : Finset α) (T : Finset β)
    (hT : T ∈ (S'.map e).powersetCard 2) :
    ∃ U ∈ S'.powersetCard 2, U.map e = T := by
  classical
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hsub, hcard⟩ := hT
  let U : Finset α := S'.filter (fun j => e j ∈ T)
  have hmap : U.map e = T := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨a, haU, rfl⟩ := hx
      rw [Finset.mem_filter] at haU
      exact haU.2
    · intro hx
      have hxmap : x ∈ S'.map e := hsub hx
      rw [Finset.mem_map] at hxmap
      obtain ⟨a, haS, rfl⟩ := hxmap
      rw [Finset.mem_map]
      refine ⟨a, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨haS, hx⟩
  have hUcard : U.card = 2 := by
    have h1 : U.card = (U.map e).card := (Finset.card_map e).symm
    rw [hmap, hcard] at h1
    exact h1
  have hUmem : U ∈ S'.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _, hUcard⟩
  exact ⟨U, hUmem, hmap⟩

private theorem insert_mono_two {N r : ℕ} (v : Fin N) (S : Finset (Fin N))
    (φ : Finset (Fin N) → Fin r) (i : Fin r)
    (hSmono : ∀ T ∈ S.powersetCard 2, φ T = i)
    (hstar : ∀ w ∈ S, φ {v, w} = i) :
    ∀ T ∈ (insert v S).powersetCard 2, φ T = i := by
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hsub, hcard⟩ := hT
  by_cases hv : v ∈ T
  · -- v ∈ T: T = {v, w} for w ∈ S
    have hcard1 : (T.erase v).card = 1 := by
      rw [Finset.card_erase_of_mem hv, hcard]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
    have hwmem : w ∈ T.erase v := by
      rw [hw]
      exact Finset.mem_singleton.mpr rfl
    have hwT : w ∈ T := Finset.mem_of_mem_erase hwmem
    have hwne : w ≠ v := (Finset.mem_erase.mp hwmem).1
    have hwIns : w ∈ insert v S := hsub hwT
    rw [Finset.mem_insert] at hwIns
    obtain rfl | hwS := hwIns
    · exact absurd rfl hwne
    · have hTeq : T = {v, w} := by
        have hins : insert v (T.erase v) = T := Finset.insert_erase hv
        rw [hw] at hins
        exact hins.symm
      rw [hTeq]
      exact hstar w hwS
  · -- v ∉ T: T ⊆ S
    have hsubS : T ⊆ S := by
      intro x hxT
      have hxIns : x ∈ insert v S := hsub hxT
      rw [Finset.mem_insert] at hxIns
      obtain rfl | hxS := hxIns
      · exact absurd hxT hv
      · exact hxS
    have hTmem : T ∈ S.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      exact ⟨hsubS, hcard⟩
    exact hSmono T hTmem

private theorem zero_vacuous (φ : Finset (Fin 0) → Fin 1) (i₀ : Fin 1) :
    ∀ T ∈ (∅ : Finset (Fin 0)).powersetCard 2, φ T = i₀ := by
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hsub, hcard⟩ := hT
  have hempty : T = ∅ := Finset.subset_empty.mp hsub
  subst hempty
  simp [Finset.card_empty] at hcard

private def RamseyProp (r : ℕ) (t : Fin r → ℕ) : Prop :=
  ∃ N : ℕ, ∀ φ : Finset (Fin N) → Fin r,
    ∃ i, ∃ S : Finset (Fin N), S.card = t i ∧ ∀ T ∈ S.powersetCard 2, φ T = i

private theorem ramsey_aux {r : ℕ} (hr : 0 < r) (t : Fin r → ℕ) :
    RamseyProp r t := by
  suffices h : ∀ s, ∀ u : Fin r → ℕ, (∑ i, u i) = s → RamseyProp r u from
    h _ t rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro u hsum
    by_cases h0 : ∃ i, u i = 0
    · obtain ⟨i₀, hi₀⟩ := h0
      exact ⟨0, fun φ => ⟨i₀, ∅, by simp [hi₀], fun T hT => by
        rw [Finset.mem_powersetCard] at hT
        obtain ⟨hsub, hcard⟩ := hT
        rw [Finset.subset_empty.mp hsub, Finset.card_empty] at hcard
        omega⟩⟩
    · push Not at h0
      classical
      have h1 : ∀ i, 1 ≤ u i := fun i => Nat.one_le_iff_ne_zero.mpr (h0 i)
      have i₀ : Fin r := ⟨0, hr⟩
      have hs1 : 1 ≤ s := by
        have hle : u i₀ ≤ ∑ i, u i := by
          have h := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀) (f := u)
          simpa using h
        have h1i := h1 i₀
        omega
      have hdec : ∀ i, (∑ j, Function.update u i (u i - 1) j) = s - 1 := by
        intro i
        have h := sum_update_decr u i (h1 i)
        omega
      have hex : ∀ i : Fin r, ∃ N : ℕ, ∀ φ : Finset (Fin N) → Fin r,
          ∃ j, ∃ S : Finset (Fin N), S.card = (Function.update u i (u i - 1)) j ∧
            ∀ T ∈ S.powersetCard 2, φ T = j := by
        intro i
        have hlt : s - 1 < s := by omega
        have h := ih (s - 1) hlt (Function.update u i (u i - 1)) (hdec i)
        obtain ⟨N, hN⟩ := h
        exact ⟨N, hN⟩
      let Nf : Fin r → ℕ := fun i => Classical.choose (hex i)
      have hNf : ∀ i, ∀ φ : Finset (Fin (Nf i)) → Fin r,
          ∃ j, ∃ S : Finset (Fin (Nf i)),
            S.card = (Function.update u i (u i - 1)) j ∧
              ∀ T ∈ S.powersetCard 2, φ T = j :=
        fun i => Classical.choose_spec (hex i)
      refine ⟨(∑ i, Nf i) + 1, ?_⟩
      set N := (∑ i, Nf i) + 1 with hNdef
      intro φ
      have hNpos : 0 < N := by omega
      set v : Fin N := ⟨0, hNpos⟩ with hvdef
      have hsum : (∑ i, (((Finset.univ.erase v).filter (fun w => φ {v, w} = i)).card))
          = ∑ i, Nf i := by
        rw [fiber_card_sum, erase_card_eq]
        omega
      obtain ⟨i, hi⟩ := exists_large_fiber hr
        (fun i => (((Finset.univ.erase v).filter (fun w => φ {v, w} = i)).card)) Nf hsum
      set X := (Finset.univ.erase v).filter (fun w => φ {v, w} = i) with hXdef
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hi
      have hTcard' : Fintype.card T = Nf i := by
        rw [Fintype.card_coe, hTcard]
      set e : Fin (Nf i) ↪o Fin N := Finset.orderEmbOfFin T hTcard with hedef
      have he_mem : ∀ j, e j ∈ T := fun j => Finset.orderEmbOfFin_mem T hTcard j
      have he_inj : Function.Injective e := e.injective
      set φ' : Finset (Fin (Nf i)) → Fin r := fun U => φ (U.map e.toEmbedding) with hφdef
      obtain ⟨j, S', hScard, hSmono⟩ := hNf i φ'
      set S : Finset (Fin N) := S'.map e.toEmbedding with hSdef
      have hScard' : S.card = S'.card := Finset.card_map e.toEmbedding
      have hST : ∀ y ∈ S, y ∈ T := by
        intro y hy
        rw [hSdef, Finset.mem_map] at hy
        obtain ⟨j', _, rfl⟩ := hy
        exact he_mem j'
      have hSX : ∀ y ∈ S, y ∈ X := fun y hy => hTsub (hST y hy)
      have hmono : ∀ T ∈ S.powersetCard 2, φ T = j := by
        intro T hT
        obtain ⟨U, hU, hUT⟩ := exists_map_preimage_powersetCard e.toEmbedding S' T hT
        have : φ' U = j := hSmono U hU
        rw [hφdef] at this
        simp only at this
        rw [hUT] at this
        exact this
      by_cases hji : j = i
      · rw [hji] at hScard hmono
        have hcard_eq : S.card = u i - 1 := by
          rw [hScard', hScard]
          exact Function.update_self i (u i - 1) u
        have hvS : v ∉ S := by
          intro hv
          have h2 : v ∈ (Finset.univ.erase v).filter (fun w => φ {v, w} = i) :=
            hSX v hv
          exact Finset.notMem_erase v Finset.univ (Finset.mem_filter.mp h2).1
        refine ⟨i, insert v S, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hvS, hcard_eq]
          have := h1 i
          omega
        · apply insert_mono_two v S φ i hmono
          intro w hw
          have h2 : w ∈ (Finset.univ.erase v).filter (fun w => φ {v, w} = i) :=
            hSX w hw
          exact (Finset.mem_filter.mp h2).2
      · refine ⟨j, S, ?_, hmono⟩
        rw [hScard', hScard]
        exact Function.update_of_ne hji _ _

/-- **Finite Ramsey theorem for pairs.** For every number of colors $r \ge 1$ and every natural
number $k$ there is a natural number $N$ such that for every coloring of the subsets of
$\{0, 1, \dots, N - 1\}$ with $r$ colors there are a $k$-element subset $S$ and a color $c$ such
that every $2$-element subset of $S$ has color $c$.

Source: F. P. Ramsey, On a Problem of Formal Logic, Proc. London Math. Soc.
s2-30 (1930), 264-286, DOI 10.1112/PLMS/S2-30.1.264. -/
public theorem ramsey_two_uniform {r k : ℕ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ φ : Finset (Fin N) → Fin r,
      ∃ S : Finset (Fin N), S.card = k ∧ ∃ c : Fin r, ∀ T ∈ S.powersetCard 2, φ T = c := by
  obtain ⟨N, hN⟩ := ramsey_aux hr (fun _ => k)
  exact ⟨N, fun φ => by
    obtain ⟨i, S, hcard, hmono⟩ := hN φ
    exact ⟨S, hcard, i, hmono⟩⟩

end MathlibExt.Combinatorics.Ramsey
