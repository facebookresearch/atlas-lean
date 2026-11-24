/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.QuadraticForm.PfisterRoundness

/-!
# Half-dimensional isotropic subspaces of Pfister forms

Every non-anisotropic explicit subset-indexed Pfister form has a
half-dimensional totally isotropic subspace.  We also expose the concrete
submodule form needed by the norm-neighbor intersection argument, with rank
exactly half the Pfister carrier dimension.

The proof is characteristic-free and valid for every tuple length at least
one.  This file defines no norm-quadric point, symbol splitting, motive,
VM2, or norm-residue theorem.

## Main declarations

* `QuadraticForm.pfister_hasHalfDimensionalTotallyIsotropicSubspace`
* `QuadraticForm.pfister_exists_halfDimensionalTotallyIsotropic`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace QuadraticForm

/-- A non-anisotropic explicit Pfister form has a half-dimensional totally
isotropic subspace. -/
theorem pfister_hasHalfDimensionalTotallyIsotropicSubspace
    (F : Type u) [Field F]
    {n : ℕ} (a : Fin (n + 1) → Fˣ)
    (h : ¬ (pfister F a).Anisotropic) :
    (pfister F a).HasHalfDimensionalTotallyIsotropicSubspace := by
  induction n with
  | zero =>
      exact
        hasHalfDimensionalTotallyIsotropicSubspace_of_not_anisotropic_finrank_two
          (pfister F a) (finrank_pfister_carrier F 1) h
  | succ n ih =>
      let lower : Fin (n + 1) → Fˣ := fun i => a i.castSucc
      let c : F := a (Fin.last (n + 1))
      let Q := pfister F lower
      let e := pfisterSuccEquiv F a
      have hc : c ≠ 0 := Units.ne_zero (a (Fin.last (n + 1)))
      have hround : Q.IsRound := pfister_isRound F lower
      have hprod : ¬ (Q.prod ((-c) • Q)).Anisotropic := by
        intro hp
        apply h
        exact e.anisotropic_iff.mpr hp
      have hP : HasHalfDimensionalTotallyIsotropicSubspace
          (Q.prod ((-c) • Q)) :=
        hasHalfDimensionalTotallyIsotropicSubspace_prod_neg_smul_of_not_anisotropic
          Q c hc hround (fun hlow => ih lower hlow) hprod
      exact hP.map_isometryEquiv e.symm

/-- A non-anisotropic explicit Pfister form has a concrete totally isotropic
submodule of rank exactly half the ambient Pfister dimension. -/
theorem pfister_exists_halfDimensionalTotallyIsotropic
    (F : Type u) [Field F]
    {n : ℕ} (a : Fin (n + 1) → Fˣ)
    (h : ¬ (pfister F a).Anisotropic) :
    ∃ H : Submodule F (Finset (Fin (n + 1)) → F),
      Module.finrank F H = 2 ^ n ∧
        ∀ x ∈ H, pfister F a x = 0 := by
  obtain ⟨_, H, hHiso, hHdim⟩ :=
    pfister_hasHalfDimensionalTotallyIsotropicSubspace F a h
  refine ⟨H, ?_, hHiso⟩
  rw [finrank_pfister_carrier, pow_succ] at hHdim
  omega

end QuadraticForm

end
