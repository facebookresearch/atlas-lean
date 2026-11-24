/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Combinatorics.Compactness
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Lattice.Nat

@[expose] public section

section
namespace MathlibExt.Combinatorics.ParisHarringtonWanted

/-!
# Paris–Harrington theorem

Proves the finite Paris–Harrington Ramsey theorem with the largeness condition.
-/

/-- Infinite Ramsey theorem, relativized to an infinite set: every finite coloring
of the `k`-subsets of an infinite `X ⊆ ℕ` admits an infinite homogeneous subset. -/
private lemma ramsey_inf : ∀ (k : ℕ) (c : ℕ) (ψ : Finset ℕ → Fin c) (X : Set ℕ),
    X.Infinite →
    ∃ H : Set ℕ, H ⊆ X ∧ H.Infinite ∧ ∃ t : Fin c,
      ∀ S : Finset ℕ, ↑S ⊆ H → S.card = k → ψ S = t := by
  intro k
  induction k with
  | zero =>
      intro c ψ X hX
      exact ⟨X, subset_rfl, hX, ψ ∅, fun S _ hcard => by
        have hS : S = ∅ := Finset.card_eq_zero.mp hcard
        rw [hS]⟩
  | succ k ih =>
      intro c χ X hX
      have step : ∀ Y : {Y : Set ℕ // Y.Infinite ∧ Y ⊆ X}, ∃ Z : {Y : Set ℕ // Y.Infinite ∧ Y ⊆ X},
          ∃ a : ℕ, ∃ t : Fin c, a ∈ Y.1 ∧ Z.1 ⊆ {x ∈ Y.1 | a < x} ∧
            ∀ S : Finset ℕ, ↑S ⊆ Z.1 → S.card = k → χ (insert a S) = t := by
        intro Y
        obtain ⟨Yv, hYinf, hYsub⟩ := Y
        obtain ⟨a, ha⟩ := hYinf.nonempty
        have hY1inf : {x ∈ Yv | a < x}.Infinite := by
          have hdiff : (Yv \ Set.Iic a).Infinite := hYinf.sdiff (Set.finite_Iic a)
          have hle : Yv \ Set.Iic a ⊆ {x ∈ Yv | a < x} := by
            intro x hx
            rw [Set.mem_sdiff, Set.mem_Iic] at hx
            rw [Set.mem_sep_iff]
            exact ⟨hx.1, lt_of_not_ge hx.2⟩
          exact Set.Infinite.mono hle hdiff
        obtain ⟨H, hHX, hHinf, t, hhom⟩ :=
          ih c (fun Sb => χ (insert a Sb)) {x ∈ Yv | a < x} hY1inf
        refine ⟨⟨H, hHinf, fun x hx => hYsub ((Set.mem_sep_iff.mp (hHX hx)).1)⟩,
          a, t, ha, hHX, ?_⟩
        intro S hS hcard
        exact hhom S hS hcard
      choose G hG using step
      set Ys : ℕ → {Y : Set ℕ // Y.Infinite ∧ Y ⊆ X} :=
        fun n => G^[n] ⟨X, hX, subset_rfl⟩ with hYs
      set Y : ℕ → Set ℕ := fun n => (Ys n).1 with hY
      have hYinf : ∀ n, (Y n).Infinite := fun n => (Ys n).2.1
      have hYsubX : ∀ n, Y n ⊆ X := fun n => (Ys n).2.2
      have wit : ∀ n, ∃ a : ℕ, ∃ t : Fin c, a ∈ Y n ∧ Y (n + 1) ⊆ {x ∈ Y n | a < x} ∧
          ∀ S : Finset ℕ, ↑S ⊆ Y (n + 1) → S.card = k → χ (insert a S) = t := by
        intro n
        have h := hG (Ys n)
        have heq : Ys (n + 1) = G (Ys n) := by
          have h1 : n + 1 = n.succ := rfl
          simp only [hYs]
          rw [h1, Function.iterate_succ_apply']
        rw [← heq] at h
        exact h
      choose a t hamem hsub hhom using wit
      have hYmono : ∀ n, Y (n + 1) ⊆ Y n :=
        fun n => fun x hx => (Set.mem_sep_iff.mp (hsub n hx)).1
      have hYanti : Antitone Y := antitone_nat_of_succ_le hYmono
      have hastrict : StrictMono a := strictMono_nat_of_lt_succ (fun n => by
        have h1 : a (n + 1) ∈ Y (n + 1) := hamem (n + 1)
        have h2 := hsub n h1
        exact (Set.mem_sep_iff.mp h2).2)
      obtain ⟨tstar, hfib⟩ := Finite.exists_infinite_fiber t
      have hIinf : (t ⁻¹' {tstar}).Infinite := Set.infinite_coe_iff.mp hfib
      set I : Set ℕ := t ⁻¹' {tstar} with hI
      set A : Set ℕ := a '' I with hA
      have hAsub : A ⊆ X := by
        intro x hx
        obtain ⟨n, hn, rfl⟩ := hx
        exact hYsubX n (hamem n)
      have hAinf : A.Infinite :=
        Set.Infinite.image hastrict.injective.injOn hIinf
      refine ⟨A, hAsub, hAinf, tstar, ?_⟩
      intro U hUA hUcard
      have hUpos : 0 < U.card := by rw [hUcard]; exact Nat.succ_pos k
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hUpos
      have huA : u ∈ A := hUA (Finset.mem_coe.mpr hu)
      obtain ⟨i, hi, rfl⟩ := huA
      set J : Set ℕ := {j ∈ I | a j ∈ U} with hJ
      have hiJ : i ∈ J := ⟨hi, hu⟩
      have hJne : J.Nonempty := ⟨i, hiJ⟩
      set i0 : ℕ := sInf J with hi0
      have hi0J : i0 ∈ J := Nat.sInf_mem hJne
      have hi0min : ∀ j ∈ J, i0 ≤ j := fun j hj => Nat.sInf_le hj
      obtain ⟨hi0I, hi0U⟩ := hi0J
      have hti0 : t i0 = tstar := Set.mem_singleton_iff.mp hi0I
      set V : Finset ℕ := U.erase (a i0) with hV
      have hVcard : V.card = k := by
        rw [hV, Finset.card_erase_of_mem hi0U, hUcard, Nat.add_sub_cancel]
      have hUeq : insert (a i0) V = U := Finset.insert_erase hi0U
      have hVsub : ↑V ⊆ Y (i0 + 1) := by
        intro x hx
        have hxV : x ∈ V := Finset.mem_coe.mp hx
        have hxU : x ∈ U := Finset.erase_subset _ _ hxV
        have hxA : x ∈ A := hUA (Finset.mem_coe.mpr hxU)
        obtain ⟨j, hjI, hjx⟩ := hxA
        have hjU : a j ∈ U := by rw [hjx]; exact hxU
        have hjJ : j ∈ J := ⟨hjI, hjU⟩
        have hle : i0 ≤ j := hi0min j hjJ
        have hne : j ≠ i0 := by
          rintro hcon
          subst hcon
          exact (Finset.ne_of_mem_erase hxV) hjx.symm
        have hlt : i0 + 1 ≤ j := Nat.succ_le_of_lt (lt_of_le_of_ne' hle hne)
        have hmem : a j ∈ Y j := hamem j
        have hmono : Y j ⊆ Y (i0 + 1) := hYanti hlt
        rw [← hjx]
        exact hmono hmem
      have hhomV := hhom i0 V hVsub hVcard
      rw [← hUeq, hhomV, hti0]

/--
**Strengthened finite Ramsey theorem (Paris–Harrington principle).** For all integers $c \ge 1$,
$k \ge 1$ and $m \ge 1$ there is a natural number $N$ such that for every coloring $f$ of the
finite subsets of $\mathbb{N}$ with $c$ colors there is a nonempty set $H \subseteq \{1, \dots, N\}$
with $|H| \ge m$ and $\min H \le |H|$ such that all $k$-element subsets of $H$ have the same color:
some color $t$ satisfies $f(S) = t$ for every $k$-element subset $S \subseteq H$.

Proves `Wanted` entry `paris_harrington`.

Source: J. Paris and L. Harrington, Handbook of Mathematical
Logic, ed. Barwise (1977); Graham-Rothschild-Spencer, Ramsey Theory; Lean states finite
combinatorial form with largeness condition, PA-independence not formalized.
-/
theorem paris_harrington :
    ∀ c k m : ℕ, 0 < c → 0 < k → 0 < m → ∃ N : ℕ,
      ∀ f : Finset ℕ → Fin c,
        ∃ H : Finset ℕ, ∃ hH : H.Nonempty,
          H ⊆ Finset.Icc 1 N ∧
          m ≤ H.card ∧
          H.min' hH ≤ H.card ∧
          ∃ t : Fin c, ∀ S : Finset ℕ, S ⊆ H → S.card = k → f S = t := by
  intro c k m hc hk hm
  by_contra hcon
  have bad : ∀ N : ℕ, ∃ f : Finset ℕ → Fin c, ∀ H : Finset ℕ, ∀ hH : H.Nonempty,
      H ⊆ Finset.Icc 1 N → m ≤ H.card → H.min' hH ≤ H.card →
      ∀ t : Fin c, ∃ S : Finset ℕ, S ⊆ H ∧ S.card = k ∧ f S ≠ t := by
    by_contra h
    push Not at h
    exact hcon h
  choose f hf using bad
  set Nof : Finset (Finset ℕ) → ℕ := fun T => (T.biUnion id).sup id with hNof
  set g : Finset (Finset ℕ) → Finset ℕ → Fin c := fun T S => f (Nof T) S with hg
  obtain ⟨χ, hχ⟩ := Finset.rado_selection g
  obtain ⟨Hset, hHsub, hHinf, tstar, hhom⟩ :=
    ramsey_inf k c χ Set.univ Set.infinite_univ
  have hZinf : (Hset ∩ Set.Ici 1).Infinite := by
    have hsub : Hset \ {0} ⊆ Hset ∩ Set.Ici 1 := by
      intro x hx
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hx
      exact ⟨hx.1, Nat.one_le_iff_ne_zero.mpr hx.2⟩
    exact Set.Infinite.mono hsub (hHinf.sdiff (Set.finite_singleton 0))
  obtain ⟨z0, hz0, hz0min⟩ :
      ∃ z0 ∈ Hset ∩ Set.Ici 1, ∀ x ∈ Hset ∩ Set.Ici 1, z0 ≤ x :=
    ⟨sInf _, Nat.sInf_mem hZinf.nonempty, fun x hx => Nat.sInf_le hx⟩
  have hz0H : z0 ∈ Hset := hz0.1
  have hz01 : 1 ≤ z0 := hz0.2
  obtain ⟨Sp, hSpZ, hSpcard⟩ :=
    (hZinf.sdiff (Set.finite_singleton z0)).exists_subset_card_eq (m + z0)
  set Hp : Finset ℕ := insert z0 Sp with hHp
  have hz0Sp : z0 ∉ Sp := by
    intro hcon
    have hmem := hSpZ (Finset.mem_coe.mpr hcon)
    rw [Set.mem_sdiff, Set.mem_singleton_iff] at hmem
    exact hmem.2 rfl
  have hHpcard : Hp.card = m + z0 + 1 := by
    rw [hHp, Finset.card_insert_of_notMem hz0Sp, hSpcard]
  have hHpne : Hp.Nonempty := by
    rw [← Finset.card_pos, hHpcard]
    omega
  have hmin : Hp.min' hHpne = z0 := by
    apply le_antisymm
    · exact Finset.min'_le Hp z0 (Finset.mem_insert_self z0 Sp)
    · apply Finset.le_min'
      intro y hy
      rw [hHp, Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact le_rfl
      · have hyZ : y ∈ Hset ∩ Set.Ici 1 := by
          have hmem := hSpZ (Finset.mem_coe.mpr hy)
          rw [Set.mem_sdiff] at hmem
          exact hmem.1
        exact hz0min y hyZ
  have hHpsub : ↑Hp ⊆ Hset := by
    intro y hy
    have hyF : y ∈ Hp := Finset.mem_coe.mp hy
    rw [hHp, Finset.mem_insert] at hyF
    rcases hyF with rfl | hyF
    · exact hz0H
    · have hmem := hSpZ (Finset.mem_coe.mpr hyF)
      rw [Set.mem_sdiff] at hmem
      exact hmem.1.1
  have hHpge : ∀ y ∈ Hp, 1 ≤ y := by
    intro y hy
    rw [hHp, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hz01
    · have hmem := hSpZ (Finset.mem_coe.mpr hy)
      rw [Set.mem_sdiff] at hmem
      exact hmem.1.2
  have hHphom : ∀ S : Finset ℕ, S ⊆ Hp → S.card = k → χ S = tstar := by
    intro S hS hcard
    apply hhom
    · intro y hy
      have h1 : y ∈ S := Finset.mem_coe.mp hy
      have h2 : y ∈ Hp := hS h1
      exact hHpsub (Finset.mem_coe.mpr h2)
    · exact hcard
  set s0 : Finset (Finset ℕ) := insert Hp (Finset.powersetCard k Hp) with hs0
  obtain ⟨t, htsub, htagree⟩ := hχ s0
  set N : ℕ := (t.biUnion id).sup id with hN
  have hHpmem : Hp ∈ t := htsub (Finset.mem_insert_self Hp _)
  have hHpU : Hp ⊆ t.biUnion id := Finset.subset_biUnion_of_mem id hHpmem
  have hHpIcc : Hp ⊆ Finset.Icc 1 N := by
    intro y hy
    rw [Finset.mem_Icc]
    exact ⟨hHpge y hy, Finset.le_sup (f := id) (hHpU hy)⟩
  have hagree : ∀ S : Finset ℕ, S ⊆ Hp → S.card = k → f N S = χ S := by
    intro S hS hcard
    have hmem0 : S ∈ s0 :=
      Finset.mem_insert_of_mem (Finset.mem_powersetCard.mpr ⟨hS, hcard⟩)
    have h1 : χ S = f N S := htagree S hmem0
    exact h1.symm
  have hcard : m ≤ Hp.card := by rw [hHpcard]; omega
  have hmin2 : Hp.min' hHpne ≤ Hp.card := by rw [hmin, hHpcard]; omega
  obtain ⟨S, hS1, hS2, hne⟩ := hf N Hp hHpne hHpIcc hcard hmin2 tstar
  have hcon2 : f N S = tstar := by
    rw [hagree S hS1 hS2]
    exact hHphom S hS1 hS2
  exact hne hcon2

end MathlibExt.Combinatorics.ParisHarringtonWanted
