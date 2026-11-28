/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.QuadraticForm.PfisterRoundness
public import MathlibExt.LinearAlgebra.QuadraticForm.HalfDimensionalTotallyIsotropic

/-!
# Half-dimensional isotropic subspaces of diagonal quasi-Pfister forms

Let F be a field, n ∈ ℕ and a₀,…,aₙ ∈ Fˣ. Define qₐ(x) = ∑ₛ(∏ᵢ∈s −aᵢ)xₛ² on
F^(Finset(Fin(n+1))). If qₐ is not anisotropic, there exists a subspace H on which qₐ vanishes
with dim H = 2^n, half its ambient dimension 2^(n+1). This holds over fields of arbitrary
characteristic for these diagonal quasi-Pfister forms, including the totally singular
characteristic-two case.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace QuadraticForm

/-- **Half-dimensional total isotropy of an isotropic diagonal quasi-Pfister form.**

Let F be a field, n ∈ ℕ and a₀,…,aₙ ∈ Fˣ. Define qₐ(x) = ∑ₛ(∏ᵢ∈s −aᵢ)xₛ² on
F^(Finset(Fin(n+1))). If qₐ is not anisotropic, it has a totally isotropic subspace H
satisfying 2 dim_F H = dim_F(F^(Finset(Fin(n+1)))).
-/
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

/-- **A concrete isotropic subspace of a diagonal quasi-Pfister form.**

Let F be a field, n ∈ ℕ and a₀,…,aₙ ∈ Fˣ. Define qₐ(x) = ∑ₛ(∏ᵢ∈s −aᵢ)xₛ² on
F^(Finset(Fin(n+1))). If qₐ is not anisotropic, there exists H ⊆ F^(Finset(Fin(n+1))) with
dim_F H = 2^n and qₐ(x) = 0 for every x ∈ H.
-/
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
