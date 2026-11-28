/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BlockStabilization
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Instances.Matrix

/-!
# Stabilization of finite general linear groups to a specified size

This file packages `diag(g, 1)` stabilization from size `n` directly to any
size `N` with `n ≤ N`. The construction reuses `blockStabilization` and only
reindexes its target along `n + (N - n) = N`.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uR vR

/-- Add an identity block of size `N - n` and reindex to `Fin N`. -/
def stabilizeTo
    (R : Type uR) [Semiring R] {n N : ℕ} (h : n ≤ N) :
    GL (Fin n) R →* GL (Fin N) R :=
  (reindexMulEquiv
      (finCongr (Nat.add_sub_of_le h))).toMonoidHom.comp
    (blockStabilization n (N - n) R)

/-- The matrix action of `stabilizeTo` is the literal identity-block insertion
followed by the two canonical finite reindexings. -/
@[simp]
theorem coe_stabilizeTo
    (R : Type uR) [Semiring R] {n N : ℕ} (h : n ≤ N)
    (g : GL (Fin n) R) :
    (↑(stabilizeTo R h g) : Matrix (Fin N) (Fin N) R) =
      Matrix.reindex
        (finCongr (Nat.add_sub_of_le h))
        (finCongr (Nat.add_sub_of_le h))
        (Matrix.reindex
          (finSumFinEquiv (m := n) (n := N - n))
          (finSumFinEquiv (m := n) (n := N - n))
          (Matrix.fromBlocks
            (↑g : Matrix (Fin n) (Fin n) R) 0 0 1)) :=
  rfl

/-- Stabilization to a specified size commutes with arbitrary coefficient
maps, including maps between rings in different universes. -/
theorem stabilizeTo_mapRingHom
    {R : Type uR} {S : Type vR} [Semiring R] [Semiring S]
    {n N : ℕ} (h : n ≤ N) (f : R →+* S) :
    (stabilizeTo S h).comp (mapRingHom (n := Fin n) f) =
      (mapRingHom (n := Fin N) f).comp (stabilizeTo R h) := by
  apply MonoidHom.ext
  intro g
  change
    reindexMulEquiv (A := S) (finCongr (Nat.add_sub_of_le h))
        (blockStabilization n (N - n) S (mapRingHom f g)) =
      mapRingHom f
        (reindexMulEquiv (A := R) (finCongr (Nat.add_sub_of_le h))
          (blockStabilization n (N - n) R g))
  rw [blockStabilization_mapRingHom_apply,
    reindexMulEquiv_mapRingHom_apply]

private theorem stabilizeTo_apply
    (R : Type uR) [Semiring R] {n N : ℕ} (h : n ≤ N)
    (g : GL (Fin n) R) (i j : Fin N) :
    (stabilizeTo R h g : Matrix (Fin N) (Fin N) R) i j =
      if hi : i.val < n then
        if hj : j.val < n then
          (g : Matrix (Fin n) (Fin n) R)
            ⟨i.val, hi⟩ ⟨j.val, hj⟩
        else 0
      else if j.val < n then 0
      else if i = j then 1 else 0 := by
  rw [coe_stabilizeTo]
  simp only [Matrix.reindex_apply]
  generalize hiEq :
      (finSumFinEquiv (m := n) (n := N - n)).symm
        ((finCongr (Nat.add_sub_of_le h)).symm i) = ii
  generalize hjEq :
      (finSumFinEquiv (m := n) (n := N - n)).symm
        ((finCongr (Nat.add_sub_of_le h)).symm j) = jj
  rcases ii with ii | ii <;> rcases jj with jj | jj <;>
    change Matrix.fromBlocks (↑g : Matrix (Fin n) (Fin n) R) 0 0 1
      ((finSumFinEquiv (m := n) (n := N - n)).symm
        ((finCongr (Nat.add_sub_of_le h)).symm i))
      ((finSumFinEquiv (m := n) (n := N - n)).symm
        ((finCongr (Nat.add_sub_of_le h)).symm j)) = _ <;>
    rw [hiEq, hjEq]
  · have hiVal : i.val = ii.val := by
      have hval := congrArg
        (fun x => ((finSumFinEquiv (m := n) (n := N - n)) x).val)
        hiEq
      simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left,
        Fin.val_castAdd, finCongr_symm_apply_coe] using hval
    have hjVal : j.val = jj.val := by
      have hval := congrArg
        (fun x => ((finSumFinEquiv (m := n) (n := N - n)) x).val)
        hjEq
      simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left,
        Fin.val_castAdd, finCongr_symm_apply_coe] using hval
    have hi : i.val < n := by simpa only [hiVal] using ii.isLt
    have hj : j.val < n := by simpa only [hjVal] using jj.isLt
    have hii : (⟨i.val, hi⟩ : Fin n) = ii := Fin.ext hiVal
    have hjj : (⟨j.val, hj⟩ : Fin n) = jj := Fin.ext hjVal
    simp [Matrix.fromBlocks_apply₁₁, hi, hj, hii, hjj]
  · have hiVal : i.val = ii.val := by
      have hval := congrArg
        (fun x => ((finSumFinEquiv (m := n) (n := N - n)) x).val)
        hiEq
      simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left,
        Fin.val_castAdd, finCongr_symm_apply_coe] using hval
    have hjVal : j.val = n + jj.val := by
      have hval := congrArg
        (fun x => ((finSumFinEquiv (m := n) (n := N - n)) x).val)
        hjEq
      simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right,
        Fin.val_natAdd, finCongr_symm_apply_coe] using hval
    have hi : i.val < n := by simpa only [hiVal] using ii.isLt
    have hj : ¬ j.val < n := by
      rw [hjVal]
      exact Nat.not_lt_of_ge (Nat.le_add_right n jj.val)
    simp [Matrix.fromBlocks_apply₁₂, hi, hj]
  · have hiVal : i.val = n + ii.val := by
      have hval := congrArg
        (fun x => ((finSumFinEquiv (m := n) (n := N - n)) x).val)
        hiEq
      simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right,
        Fin.val_natAdd, finCongr_symm_apply_coe] using hval
    have hjVal : j.val = jj.val := by
      have hval := congrArg
        (fun x => ((finSumFinEquiv (m := n) (n := N - n)) x).val)
        hjEq
      simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left,
        Fin.val_castAdd, finCongr_symm_apply_coe] using hval
    have hi : ¬ i.val < n := by
      rw [hiVal]
      exact Nat.not_lt_of_ge (Nat.le_add_right n ii.val)
    have hj : j.val < n := by simpa only [hjVal] using jj.isLt
    simp [Matrix.fromBlocks_apply₂₁, hi, hj]
  · have hiVal : i.val = n + ii.val := by
      have hval := congrArg
        (fun x => ((finSumFinEquiv (m := n) (n := N - n)) x).val)
        hiEq
      simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right,
        Fin.val_natAdd, finCongr_symm_apply_coe] using hval
    have hjVal : j.val = n + jj.val := by
      have hval := congrArg
        (fun x => ((finSumFinEquiv (m := n) (n := N - n)) x).val)
        hjEq
      simpa only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right,
        Fin.val_natAdd, finCongr_symm_apply_coe] using hval
    have hi : ¬ i.val < n := by
      rw [hiVal]
      exact Nat.not_lt_of_ge (Nat.le_add_right n ii.val)
    have hj : ¬ j.val < n := by
      rw [hjVal]
      exact Nat.not_lt_of_ge (Nat.le_add_right n jj.val)
    have hij : ii = jj ↔ i = j := by
      constructor
      · intro heq
        subst jj
        apply (finCongr (Nat.add_sub_of_le h)).symm.injective
        apply (finSumFinEquiv (m := n) (n := N - n)).symm.injective
        exact hiEq.trans hjEq.symm
      · intro h
        subst j
        exact Sum.inr.inj (hiEq.symm.trans hjEq)
    simp [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, hi, hj, hij]

/-- Stabilizing a finite general linear group to its current size is the
identity map. -/
@[simp]
theorem stabilizeTo_refl
    (R : Type uR) [Semiring R] (n : ℕ) (g : GL (Fin n) R) :
    stabilizeTo R (le_refl n) g = g := by
  apply Units.ext
  ext i j
  simp [stabilizeTo_apply, i.isLt, j.isLt]

/-- Successive finite target-size stabilizations equal the direct
stabilization. -/
theorem stabilizeTo_trans
    (R : Type uR) [Semiring R] {n m N : ℕ}
    (hnm : n ≤ m) (hmN : m ≤ N) (g : GL (Fin n) R) :
    stabilizeTo R hmN (stabilizeTo R hnm g) =
      stabilizeTo R (hnm.trans hmN) g := by
  apply Units.ext
  ext i j
  by_cases hin : i.val < n
  · have him : i.val < m := lt_of_lt_of_le hin hnm
    by_cases hjn : j.val < n
    · have hjm : j.val < m := lt_of_lt_of_le hjn hnm
      simp [stabilizeTo_apply, hin, him, hjn, hjm]
    · by_cases hjm : j.val < m
      · simp [stabilizeTo_apply, hin, him, hjn, hjm]
      · simp [stabilizeTo_apply, hin, him, hjn, hjm]
  · by_cases him : i.val < m
    · by_cases hjn : j.val < n
      · have hjm : j.val < m := lt_of_lt_of_le hjn hnm
        simp [stabilizeTo_apply, hin, him, hjn, hjm]
      · by_cases hjm : j.val < m
        · simp [stabilizeTo_apply, hin, him, hjn, hjm, Fin.ext_iff]
        · have hij : i ≠ j := by
            intro hij
            subst j
            exact hjm him
          simp [stabilizeTo_apply, hin, him, hjn, hjm, hij]
    · have hin' : ¬ i.val < n := fun h =>
        him (lt_of_lt_of_le h hnm)
      by_cases hjn : j.val < n
      · have hjm : j.val < m := lt_of_lt_of_le hjn hnm
        simp [stabilizeTo_apply, hin', him, hjn, hjm]
      · by_cases hjm : j.val < m
        · have hij : i ≠ j := by
            intro hij
            subst j
            exact him hjm
          simp [stabilizeTo_apply, hin', him, hjn, hjm, hij]
        · simp [stabilizeTo_apply, hin', him, hjn, hjm]

/-- Stabilization is continuous for the product topology on finite matrices. -/
theorem continuous_stabilizeTo
    (R : Type uR) [Semiring R] [TopologicalSpace R]
    {n N : ℕ} (h : n ≤ N) :
    Continuous (stabilizeTo R h) := by
  let eSum : Fin n ⊕ Fin (N - n) ≃ Fin (n + (N - n)) :=
    finSumFinEquiv
  let eTarget : Fin (n + (N - n)) ≃ Fin N :=
    finCongr (Nat.add_sub_of_le h)
  have hfromBlocks : Continuous
      (Matrix.fromBlocksOneMonoidHom R (Fin n) (Fin (N - n))) := by
    change Continuous fun A : Matrix (Fin n) (Fin n) R =>
      Matrix.fromBlocks A 0 0 1
    refine continuous_matrix fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · exact continuous_apply_apply i j
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
  have hblockDiagonal : Continuous
      (blockDiagonalOne (Fin n) (Fin (N - n)) R) := by
    change Continuous
      (Units.map (Matrix.fromBlocksOneMonoidHom R
        (Fin n) (Fin (N - n))))
    exact Continuous.units_map _ hfromBlocks
  have hreindexSumMatrix : Continuous
      (Matrix.reindexRingEquiv R eSum) := by
    change Continuous fun A : Matrix (Fin n ⊕ Fin (N - n))
        (Fin n ⊕ Fin (N - n)) R => Matrix.reindex eSum eSum A
    refine continuous_matrix fun i j => ?_
    exact continuous_apply_apply (eSum.symm i) (eSum.symm j)
  have hreindexSum : Continuous (reindexMulEquiv (A := R) eSum) := by
    change Continuous
      (Units.map (Matrix.reindexRingEquiv R eSum).toMonoidHom)
    exact Continuous.units_map _ hreindexSumMatrix
  have hblock : Continuous (blockStabilization n (N - n) R) := by
    simpa only [blockStabilization, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, eSum] using
      hreindexSum.comp hblockDiagonal
  have hreindexTargetMatrix : Continuous
      (Matrix.reindexRingEquiv R eTarget) := by
    change Continuous fun A : Matrix (Fin (n + (N - n)))
        (Fin (n + (N - n))) R =>
      Matrix.reindex eTarget eTarget A
    refine continuous_matrix fun i j => ?_
    exact continuous_apply_apply (eTarget.symm i) (eTarget.symm j)
  have hreindexTarget : Continuous
      (reindexMulEquiv (A := R) eTarget) := by
    change Continuous
      (Units.map (Matrix.reindexRingEquiv R eTarget).toMonoidHom)
    exact Continuous.units_map _ hreindexTargetMatrix
  simpa only [stabilizeTo, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    eTarget] using hreindexTarget.comp hblock

end Matrix.GeneralLinearGroup
