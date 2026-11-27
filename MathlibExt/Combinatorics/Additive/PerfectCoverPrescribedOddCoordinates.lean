/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCover
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fintype.Sum
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Perfect covers with prescribed odd coordinates

Lift a family with distinct subset sums from the quotient by an order-two subgroup, then adjoin
the subgroup's nonzero element. In the product with a cyclic 2-group, the first projection fixes
the subset from the first factor; the remaining second coordinate is represented by binary powers.

## References

* John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power of 2*,
  Journal of Integer Sequences 28 (2025), Article 25.7.8, pp. 1–18, Lemma 20 (§4, p. 11) for the
  product construction and Theorem 1 (§1) for the quotient induction.
* Béla Bajnok, Connor Berson and Hoang Anh Just, *On Perfect Bases in Finite Abelian Groups*,
  Involve 15 (2022), pp. 525–536, §4, give the earlier existence construction cited by
  Greene and Higgins.
-/

namespace MetaMathlibExt

open PerfectSubsetSumCover

private theorem injective_subsetSum_comp_equiv {ι κ G : Type*} [AddCommMonoid G]
    (e : ι ≃ κ) {s : κ → G} (hs : Function.Injective fun I : Finset κ => ∑ i ∈ I, s i) :
    Function.Injective fun I : Finset ι => ∑ i ∈ I, s (e i) := by
  intro I J h
  apply Finset.map_injective e.toEmbedding
  apply hs
  simpa only [Finset.sum_map, Equiv.toEmbedding_apply] using h

-- Projection fixes the left subset. Cancel its sum to recover the right subset.
private theorem injective_subsetSum_sumElim {ι κ G Q : Type*} [AddCommGroup G] [AddCommMonoid Q]
    (p : G →+ Q) {s : ι → G} {t : κ → G} (ht0 : ∀ j, p (t j) = 0)
    (hs : Function.Injective fun I : Finset ι => ∑ i ∈ I, p (s i))
    (ht : Function.Injective fun J : Finset κ => ∑ j ∈ J, t j) :
    Function.Injective fun U : Finset (ι ⊕ κ) => ∑ u ∈ U, Sum.elim s t u := by
  intro U V h
  simp only [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, Sum.elim_inl, Sum.elim_inr] at h
  have hleft : U.toLeft = V.toLeft := hs (by
    simpa only [map_add, map_sum, ht0, Finset.sum_const_zero, add_zero] using congrArg p h)
  rw [hleft] at h
  have hright : U.toRight = V.toRight := ht (add_left_cancel h)
  rw [← Finset.toLeft_disjSum_toRight (u := U), ← Finset.toLeft_disjSum_toRight (u := V),
    hleft, hright]

private theorem injective_subsetSum_fin_one {G : Type*} [AddCommMonoid G] {a : G} (ha : a ≠ 0) :
    Function.Injective fun I : Finset (Fin 1) => ∑ _i ∈ I, a := by
  have hshape (I : Finset (Fin 1)) : I = ∅ ∨ I = {0} := by
    by_cases h : (0 : Fin 1) ∈ I
    · right
      ext i
      simpa [Subsingleton.elim i 0] using h
    · left
      ext i
      simp [Subsingleton.elim i 0, h]
  intro I J h
  rcases hshape I with rfl | rfl <;> rcases hshape J with rfl | rfl <;> simp_all

private theorem exists_injective_subsetSum_of_card_pow_two (m : ℕ) {H : Type*}
    [AddCommGroup H] [Finite H] (hH : Nat.card H = 2 ^ m) :
    ∃ s : Fin m → H, Function.Injective fun I : Finset (Fin m) => ∑ i ∈ I, s i := by
  classical
  induction m generalizing H with
  | zero => exact ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩
  | succ m ih =>
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card' (G := H) 2 (by simp [hH, pow_succ])
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    let A := AddSubgroup.zmultiples a
    have hA : Nat.card A = 2 := by
      let : Fintype H := Fintype.ofFinite H
      rw [Nat.card_eq_fintype_card, Fintype.card_zmultiples, ha]
    have hQ : Nat.card (H ⧸ A) = 2 ^ m := by
      have h := A.card_eq_card_quotient_mul_card_addSubgroup
      rw [hH, pow_succ, hA] at h
      omega
    obtain ⟨q, hq⟩ := ih hQ
    let p := QuotientAddGroup.mk' A
    choose s hs using fun i => QuotientAddGroup.mk'_surjective A (q i)
    have hp (i : Fin m) : p (s i) = q i := hs i
    have hp0 : p a = 0 := (QuotientAddGroup.eq_zero_iff (N := A) a).mpr
      (AddSubgroup.mem_zmultiples a)
    have hinj := injective_subsetSum_sumElim p (s := s) (t := fun _ : Fin 1 => a)
      (fun _ => hp0) (by simpa only [hp] using hq) (injective_subsetSum_fin_one ha0)
    exact ⟨_, injective_subsetSum_comp_equiv finSumFinEquiv.symm hinj⟩

private theorem injective_subsetSum_two_pow (n : ℕ) :
    Function.Injective fun I : Finset (Fin n) => ∑ i ∈ I, ((2 ^ i.val : ℕ) : ZMod (2 ^ n)) := by
  let e : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hlt (I : Finset (Fin n)) : (∑ i ∈ I, (2 : ℕ) ^ i.val) < 2 ^ n := by
    rw [← show (∑ i ∈ I.map e, (2 : ℕ) ^ i) = ∑ i ∈ I, (2 : ℕ) ^ i.val by
      simp [Finset.sum_map, e]]
    exact Nat.geomSum_lt (by decide) (by simp [e])
  intro I J h
  have hcast : ((∑ i ∈ I, (2 : ℕ) ^ i.val : ℕ) : ZMod (2 ^ n)) =
      ((∑ i ∈ J, (2 : ℕ) ^ i.val : ℕ) : ZMod (2 ^ n)) := by
    simpa only [Nat.cast_sum] using h
  apply Finset.map_injective e
  apply Finset.geomSum_injective (n := 2) le_rfl
  simpa only [Finset.sum_map, e, Function.Embedding.coeFn_mk, ZMod.val_natCast_of_lt (hlt I),
    ZMod.val_natCast_of_lt (hlt J)] using congrArg ZMod.val hcast

private theorem isPerfectCover_map_univ {ι G : Type*} [Fintype ι] [AddCommGroup G]
    [DecidableEq G] [Fintype G] (e : ι ↪ G) (hcard : Fintype.card (Finset ι) = Fintype.card G)
    (he : Function.Injective fun I : Finset ι => ∑ i ∈ I, e i) :
    IsPerfectCover (Finset.univ.map e) := by
  let S : Finset G := Finset.univ.map e
  let f : ι ≃ S := (Equiv.ofInjective e e.injective).trans
    (Equiv.subtypeEquivRight fun x => by simp [S, Finset.mem_map, Set.mem_range])
  have hf (i : ι) : (f i : G) = e i := rfl
  have hinj : Function.Injective fun I : Finset S => ∑ x ∈ I, (x : G) := by
    have h := injective_subsetSum_comp_equiv f.symm he
    simpa only [← hf, Equiv.apply_symm_apply] using h
  have hsurj : Function.Surjective fun I : Finset S => ∑ x ∈ I, (x : G) :=
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨hinj, by rw [← Fintype.card_congr (Equiv.finsetCongr f), hcard]⟩).2
  intro g
  obtain ⟨I, hI⟩ := hsurj g
  change coverCount (fun x : S => (x : G)) g = 1
  rw [coverCount, Finset.card_eq_one]
  refine ⟨I, ?_⟩
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hJ => hinj (hJ.trans hI.symm), fun h => h ▸ hI⟩

/-- **Perfect covers with a prescribed number of odd last coordinates.** Let $H$ be a finite
abelian group of order $2^m$, let $n \ge 1$, and let $G = H \oplus \mathbb{Z}_{2^n}$. For every
$k$ with $1 \le k \le m + 1$, some perfect cover $S$ of $G$ has exactly $k$ elements $(h, y)$
whose coordinate $y \in \mathbb{Z}_{2^n}$ is odd.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 20
(`jis-2025-25.7.8-lem-20`). The setting `G = H ⊕ ℤ_{2^n}`, `|H| = 2^m`, is the one fixed
before the lemma in Section 4; `y` odd means `y.val` odd; `n ≥ 1` added (for `n = 0` no `y` is
odd). -/
public theorem exists_isPerfectCover_card_odd {H : Type*} [AddCommGroup H]
    [DecidableEq H] [Fintype H] {m n k : ℕ} (hH : Fintype.card H = 2 ^ m) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hkm : k ≤ m + 1) :
    ∃ S : Finset (H × ZMod (2 ^ n)),
      IsPerfectCover S ∧ (S.filter fun x => Odd x.2.val).card = k := by
  obtain ⟨s, hs⟩ := exists_injective_subsetSum_of_card_pow_two m (H := H)
    (by simpa only [Nat.card_eq_fintype_card] using hH)
  let l (i : Fin m) : H × ZMod (2 ^ n) := (s i, if i.val < k - 1 then 1 else 0)
  let r (j : Fin n) : H × ZMod (2 ^ n) := (0, (2 ^ j.val : ℕ))
  have hr : Function.Injective fun I : Finset (Fin n) => ∑ j ∈ I, r j := by
    intro I J h
    apply injective_subsetSum_two_pow n
    simpa only [Prod.snd_sum, r] using congrArg Prod.snd h
  have hinj := injective_subsetSum_sumElim (AddMonoidHom.fst H (ZMod (2 ^ n)))
    (s := l) (t := r) (fun _ => rfl) hs hr
  -- Distinct singleton sums let us forget the indices without losing any elements.
  let e : (Fin m ⊕ Fin n) ↪ H × ZMod (2 ^ n) := ⟨Sum.elim l r, fun i j h => by
    simpa only [Finset.sum_singleton, Finset.singleton_inj] using
      (hinj (a₁ := {i}) (a₂ := {j}) (by simpa only [Finset.sum_singleton] using h))⟩
  refine ⟨Finset.univ.map e, isPerfectCover_map_univ e ?_ hinj, ?_⟩
  · simp [Fintype.card_finset, Fintype.card_prod, hH, ZMod.card, pow_add]
  · rw [Finset.filter_map, Finset.card_map]
    have hmod : 1 < (2 : ℕ) ^ n := one_lt_pow₀ (by decide) (by omega)
    have h1 := ZMod.val_one'' (Ne.symm hmod.ne)
    let T := (Finset.univ : Finset (Fin m ⊕ Fin n)).filter fun j => Odd (e j).2.val
    have hleft : T.toLeft = (Finset.univ.filter fun i : Fin m => i.val < k - 1) := by
      ext i
      simp only [T, Finset.mem_toLeft, Finset.mem_filter, Finset.mem_univ, true_and]
      change Odd (l i).2.val ↔ i.val < k - 1
      by_cases hi : i.val < k - 1 <;> simp [l, h1, hi]
    have hright : T.toRight = {⟨0, by omega⟩} := by
      ext j
      simp only [T, Finset.mem_toRight, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, Fin.ext_iff]
      change Odd (((2 ^ j.val : ℕ) : ZMod (2 ^ n)).val) ↔ j.val = 0
      rw [ZMod.val_natCast_of_lt (pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) j.isLt)]
      cases j.val <;> simp [pow_succ, Nat.odd_mul]
    change T.card = k
    rw [← Finset.card_toLeft_add_card_toRight, hleft, hright, Fin.card_filter_val_lt,
      Nat.min_eq_right (by omega : k - 1 ≤ m), Finset.card_singleton]
    omega

end MetaMathlibExt
