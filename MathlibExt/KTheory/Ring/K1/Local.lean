/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Local
public import MathlibExt.KTheory.Ring.K1.Determinant
public import MathlibExt.KTheory.Ring.K1.Whitehead

/-! # K₁ of a commutative local ring via determinant -/

@[expose] public section

universe u

namespace AlgebraicKTheory

noncomputable section

variable (R : Type u) [CommRing R] [IsLocalRing R]

private theorem ker_det_le_stableElementary :
    MonoidHom.ker (StableGL.det (R := R)) ≤ stableElementarySubgroup R := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  obtain ⟨n, g, rfl⟩ := StableGL.exists_finite_rep (R := R) x
  have hg_det : Matrix.GeneralLinearGroup.det g = 1 := by
    have h : StableGL.det (R := R) (StableGL.of g) = 1 := hx
    rw [StableGL.det_of] at h
    exact h
  have hg_mem : g ∈ Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R :=
    Matrix.GeneralLinearGroup.mem_elementarySubgroup_of_det_eq_one_of_isLocalRing hg_det
  have h_mem : StableGL.of g ∈ stableElementarySubgroup R := by
    have h0 := StableE.fromFinite_mem (R := R) n hg_mem
    have h1 : ((StableGL.inclusion n).app (SemiRingCat.of R)).hom g =
        StableGL.of g := rfl
    rw [h1] at h0
    exact h0
  exact h_mem

/-- Stable elementary subgroup equals kernel of stable determinant
    over a commutative local ring. -/
theorem stableElementarySubgroup_eq_ker_det_of_isLocalRing :
    stableElementarySubgroup R = MonoidHom.ker (StableGL.det (R := R)) :=
  le_antisymm (stableElementarySubgroup_le_ker_det R) (ker_det_le_stableElementary R)

/-- Determinant on `K₁` is injective over a commutative local ring. -/
theorem K1.detHom_injective_of_isLocalRing :
    Function.Injective (K1.detHom (R := R)) := by
  have hCommKer : commutator (StableGL R) = MonoidHom.ker (StableGL.det (R := R)) := by
    rw [← stableElementarySubgroup_eq_commutator R,
      stableElementarySubgroup_eq_ker_det_of_isLocalRing R]
  exact K1.detHom_injective_of_commutator_eq_ker hCommKer

/-- Determinant equivalence `K₁ R ≃+ Additive Rˣ` for a commutative local ring. -/
noncomputable def K1.detEquivUnitsOfLocalRing :
    K1 R ≃+ Additive Rˣ :=
  AddEquiv.ofBijective (K1.detHom (R := R))
    ⟨K1.detHom_injective_of_isLocalRing R, K1.detHom_surjective R⟩

@[simp]
theorem K1.detEquivUnitsOfLocalRing_apply (x : K1 R) :
    K1.detEquivUnitsOfLocalRing (R := R) x = K1.detHom (R := R) x :=
  rfl

end

end AlgebraicKTheory

end
