/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

@[expose] public section

/-!
# Kleinberg clustering impossibility, source-to-statement interface

Source: Jon Kleinberg, An Impossibility Theorem for Clustering (2002), Section 2,
Definitions and Theorem 2.1.

Point set `{1, …, n}` is `Fin n` (relabeling `0..n-1`). A distance function is
`Dissimilarity`: symmetric matrix, zero diagonal, strictly positive off-diagonal,
without a triangle-inequality axiom (hence not a `MetricSpace`). Partitions are
`Setoid (Fin n)`; Mathlib's `Setoid.Partition.orderIso` in
`Mathlib.Order.Setoid.Partition` (not imported here) bridges them to sets of blocks.

Clause map: `α·d` is `Dissimilarity.scale` (`scale_apply` is evaluation);
Scale-Invariance is `ScaleInvariant`; Richness (`Range(f)` is all partitions) is
`Function.Surjective f`; `Γ`-transformation is `IsGammaTransform`
(same-cluster `Γ.r` pairs do not increase, different-cluster `¬ Γ.r` pairs do not
decrease); Consistency is `Consistent`; Theorem 2.1 is `kleinberg_impossibility`
for every `n ≥ 2` (the `n = 1` exception is the `2 ≤ n` hypothesis).
-/

namespace Cslib.MachineLearning.Clustering

/-- Finite dissimilarity on `Fin n`, without a triangle-inequality axiom:
symmetric, zero on the diagonal, strictly positive off the diagonal. -/
public structure Dissimilarity (n : Nat) where
  toFun : Fin n → Fin n → Real
  symm : ∀ (i j : Fin n), toFun i j = toFun j i
  diag : ∀ (i : Fin n), toFun i i = 0
  pos : ∀ (i j : Fin n), i ≠ j → 0 < toFun i j

/-- Positive scaling `α·d` for an explicitly positive real scalar.
Returns a valid `Dissimilarity` with complete closure proofs. -/
public noncomputable def Dissimilarity.scale (n : Nat) (d : Dissimilarity n)
    (α : Real) (hα : 0 < α) : Dissimilarity n where
  toFun := fun i j => α * d.toFun i j
  symm := fun i j => by
    show α * d.toFun i j = α * d.toFun j i
    rw [d.symm i j]
  diag := fun i => by
    show α * d.toFun i i = 0
    rw [d.diag i, mul_zero]
  pos := fun i j hne => mul_pos hα (d.pos i j hne)

/-- Observable evaluation of positive scaling:
`(scale n d α hα).toFun i j = α * d.toFun i j`. -/
public theorem Dissimilarity.scale_apply (n : Nat) (d : Dissimilarity n)
    (α : Real) (hα : 0 < α) (i j : Fin n) :
    (Dissimilarity.scale n d α hα).toFun i j = α * d.toFun i j :=
  rfl

/-- `IsGammaTransform n Γ d d'` says `d'` is a `Γ`-transformation of `d`:
same-cluster pairs (`Γ.r`) do not increase, different-cluster pairs
(`¬ Γ.r`) do not decrease. -/
public noncomputable def IsGammaTransform (n : Nat) (Γ : Setoid (Fin n))
    (d d' : Dissimilarity n) : Prop :=
  (∀ (i j : Fin n), Γ.r i j → d'.toFun i j ≤ d.toFun i j) ∧
    (∀ (i j : Fin n), ¬ Γ.r i j → d.toFun i j ≤ d'.toFun i j)

/-- Scale invariance: `f d = f (α·d)` for every distance `d` and every
explicitly positive real `α`. -/
public noncomputable def ScaleInvariant (n : Nat)
    (f : Dissimilarity n → Setoid (Fin n)) : Prop :=
  ∀ (d : Dissimilarity n) (α : Real) (hα : 0 < α),
    f d = f (Dissimilarity.scale n d α hα)

/-- Consistency: if `f d = Γ` and `d'` is a `Γ`-transformation of `d`,
then `f d' = Γ`. -/
public noncomputable def Consistent (n : Nat)
    (f : Dissimilarity n → Setoid (Fin n)) : Prop :=
  ∀ (d d' : Dissimilarity n) (Γ : Setoid (Fin n)),
    f d = Γ → IsGammaTransform n Γ d d' → f d' = Γ

/-- Kleinberg Theorem 2.1: for each `n ≥ 2`, there is no clustering function
simultaneously satisfying scale invariance, richness (`Function.Surjective`),
and consistency. -/
public theorem kleinberg_impossibility (n : Nat) (hn : 2 ≤ n) :
    ¬ ∃ (f : Dissimilarity n → Setoid (Fin n)),
      ScaleInvariant n f ∧ Function.Surjective f ∧ Consistent n f := by
  rintro ⟨f, hScale, hRich, hCons⟩
  obtain ⟨d_one, hd_one⟩ := hRich ⊤
  have hall : ∀ (d : Dissimilarity n), f d = ⊤ := by
    intro d
    have hn0 : 0 < n := by omega
    let i0 : Fin n := ⟨0, hn0⟩
    have hne_univ : (Finset.univ : Finset (Fin n × Fin n)).Nonempty :=
      ⟨(i0, i0), Finset.mem_univ _⟩
    obtain ⟨p0, _, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun p : Fin n × Fin n =>
        if p.1 = p.2 then (1 : Real)
        else d.toFun p.1 p.2 / d_one.toFun p.1 p.2 + 1)
      hne_univ
    set α : Real :=
      (if p0.1 = p0.2 then (1 : Real)
        else d.toFun p0.1 p0.2 / d_one.toFun p0.1 p0.2 + 1) with hα_def
    have hle_diag :
        (if (i0, i0).1 = (i0, i0).2 then (1 : Real)
          else d.toFun (i0, i0).1 (i0, i0).2 / d_one.toFun (i0, i0).1 (i0, i0).2 + 1) ≤ α :=
      hmax (i0, i0) (Finset.mem_univ _)
    rw [ite_eq_left rfl] at hle_diag
    have hα : 0 < α := lt_of_lt_of_le zero_lt_one hle_diag
    have hdom : ∀ (i j : Fin n), i ≠ j → d.toFun i j ≤ α * d_one.toFun i j := by
      intro i j hne
      have hle :
          (if (i, j).1 = (i, j).2 then (1 : Real)
            else d.toFun (i, j).1 (i, j).2 / d_one.toFun (i, j).1 (i, j).2 + 1) ≤ α :=
        hmax (i, j) (Finset.mem_univ _)
      have hne' : (i, j).1 ≠ (i, j).2 := hne
      rw [ite_eq_right hne'] at hle
      have hle' : d.toFun i j / d_one.toFun i j + 1 ≤ α := hle
      have hpos1 : 0 < d_one.toFun i j := d_one.pos i j hne
      have hne0 : d_one.toFun i j ≠ 0 := ne_of_gt hpos1
      have hcancel : d.toFun i j / d_one.toFun i j * d_one.toFun i j = d.toFun i j :=
        div_mul_cancel₀ _ hne0
      have hmul : (d.toFun i j / d_one.toFun i j + 1) * d_one.toFun i j ≤ α * d_one.toFun i j :=
        mul_le_mul_of_nonneg_right hle' (le_of_lt hpos1)
      have hexpand : (d.toFun i j / d_one.toFun i j + 1) * d_one.toFun i j
          = d.toFun i j + d_one.toFun i j := by
        rw [add_mul, hcancel, one_mul]
      have hle_add : d.toFun i j ≤ d.toFun i j + d_one.toFun i j :=
        le_add_of_nonneg_right (le_of_lt hpos1)
      rw [hexpand] at hmul
      exact le_trans hle_add hmul
    have hscaled : f (Dissimilarity.scale n d_one α hα) = ⊤ := by
      have hscale_eq := hScale d_one α hα
      rw [hd_one] at hscale_eq
      exact hscale_eq.symm
    have htrans : IsGammaTransform n ⊤ (Dissimilarity.scale n d_one α hα) d := by
      constructor
      · intro i j _
        by_cases hij : i = j
        · subst hij
          rw [d.diag, Dissimilarity.scale_apply, d_one.diag, mul_zero]
        · rw [Dissimilarity.scale_apply]
          exact hdom i j hij
      · intro i j hcon
        exact absurd trivial hcon
    exact hCons _ _ ⊤ hscaled htrans
  obtain ⟨d_bot, hd_bot⟩ := hRich ⊥
  have htop := hall d_bot
  rw [hd_bot] at htop
  have hab : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    have h01 : (0 : Nat) = 1 := congrArg Fin.val h
    omega
  have hbot_r : (⊥ : Setoid (Fin n)).r ⟨0, by omega⟩ ⟨1, by omega⟩ := by
    rw [htop]
    trivial
  have heq : (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := hbot_r
  exact hab heq

end Cslib.MachineLearning.Clustering
