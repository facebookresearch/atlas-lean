/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSet
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Constant local systems on simplicial sets

For a constant module-valued local system on an arbitrary simplicial set, the
nerve-pullback coefficient family is constant, all component transports are
identities, and the resulting alternating-face complex is canonically
isomorphic to Mathlib's existing simplicial chain complex.

This file stops at the unnormalized chain-complex comparison. It makes no
homology, functoriality, TopCat/CGWH, acyclicity, or plus-construction claim.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

universe uR uX

namespace SSet

variable {R : Type uR} [CommRing R]
variable {X : SSet.{uX}}
variable (M : ModuleCat.{max uR uX} R)

/-- The constant local system with value `M` on the fundamental groupoid of
`X`. -/
abbrev constantLocalSystem : SSet.LocalSystem R X :=
  (Functor.const (SSet.FundamentalGroupoid X)).obj M

/-- The coefficient family of a constant local system is pointwise `M`. -/
@[simp]
theorem constantLocalCoefficientFamily (n : ℕ) :
    localCoefficientFamily (constantLocalSystem (X := X) M) n =
      fun _ : X _⦋n⦌ => M :=
  rfl

/-- The degree object for a constant local system is a coproduct of copies of
`M` indexed by the degree-`n` simplices. -/
@[simp]
theorem constantLocalCoefficientObj (n : ℕ) :
    localCoefficientObj (constantLocalSystem (X := X) M) n =
      ∐ fun _ : X _⦋n⦌ => M :=
  rfl

/-- Inclusion of the constant coefficient summand indexed by a simplex. -/
noncomputable abbrev constantLocalCoefficientι {n : ℕ} (σ : X _⦋n⦌) :
    M ⟶ localCoefficientObj (constantLocalSystem (X := X) M) n :=
  nervePullbackCoefficientι (fundamentalGroupoidNerveUnit X)
    (constantLocalSystem (X := X) M) σ

@[simp]
theorem constantLocalCoefficientι_eq {n : ℕ} (σ : X _⦋n⦌) :
    constantLocalCoefficientι M σ =
      Sigma.ι (fun _ : X _⦋n⦌ => M) σ :=
  rfl

/-- Every face component of a constant local system is the identity. -/
@[simp]
theorem constantLocalCoefficientFaceHom {n : ℕ}
    (i : Fin (n + 2)) (σ : X _⦋n + 1⦌) :
    nervePullbackCoefficientFaceHom (fundamentalGroupoidNerveUnit X)
        (constantLocalSystem (X := X) M) i σ = 𝟙 M := by
  unfold nervePullbackCoefficientFaceHom coefficientFaceHom
  simp

/-- Every degeneracy component of a constant local system is the identity. -/
@[simp]
theorem constantLocalCoefficientDegeneracyHom {n : ℕ}
    (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    nervePullbackCoefficientDegeneracyHom (fundamentalGroupoidNerveUnit X)
        (constantLocalSystem (X := X) M) i σ = 𝟙 M := by
  unfold nervePullbackCoefficientDegeneracyHom coefficientDegeneracyHom
  simp

/-- A face map for constant local coefficients is the exact coproduct map
induced by the corresponding simplex face. -/
theorem constantLocalCoefficientFace {n : ℕ} (i : Fin (n + 2)) :
    localCoefficientFace (constantLocalSystem (X := X) M) i =
      Sigma.map' (fun σ : X _⦋n + 1⦌ => X.δ i σ) (fun _ => 𝟙 M) := by
  unfold localCoefficientFace nervePullbackCoefficientFace
  apply Sigma.map'_eq rfl
  intro σ
  rw [constantLocalCoefficientFaceHom]
  exact Category.comp_id _

/-- A degeneracy map for constant local coefficients is the exact coproduct
map induced by the corresponding simplex degeneracy. -/
theorem constantLocalCoefficientDegeneracy {n : ℕ} (i : Fin (n + 1)) :
    localCoefficientDegeneracy (constantLocalSystem (X := X) M) i =
      Sigma.map' (fun σ : X _⦋n⦌ => X.σ i σ) (fun _ => 𝟙 M) := by
  unfold localCoefficientDegeneracy nervePullbackCoefficientDegeneracy
  apply Sigma.map'_eq rfl
  intro σ
  rw [constantLocalCoefficientDegeneracyHom]
  exact Category.comp_id _

/-- Differential formula for the existing ordinary simplicial chain complex. -/
theorem constantCoefficientOrdinaryChainComplex_d (n : ℕ) :
    (X.chainComplex M).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (sigmaConst.obj M).map (X.δ i) := by
  change (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (X ⋙ sigmaConst.obj M)).d (n + 1) n = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  rfl

/-- Degreewise identity isomorphism underlying the constant-coefficient chain
comparison. -/
noncomputable abbrev constantLocalCoefficientDegreeIso (n : ℕ) :
    (localCoefficientChainComplex
        (constantLocalSystem (X := X) M)).X n ≅
      (X.chainComplex M).X n := by
  change (∐ fun _ : X _⦋n⦌ => M) ≅ (∐ fun _ : X _⦋n⦌ => M)
  exact Iso.refl _

/-- The local-coefficient complex of a constant local system is canonically
the existing simplicial chain complex. -/
noncomputable def constantLocalCoefficientChainIso :
    localCoefficientChainComplex (constantLocalSystem (X := X) M) ≅
      X.chainComplex M := by
  refine HomologicalComplex.Hom.isoOfComponents
    (constantLocalCoefficientDegreeIso M) (hf := ?_)
  rintro _ n (rfl : n + 1 = _)
  change 𝟙 _ ≫ (X.chainComplex M).d (n + 1) n =
    (localCoefficientChainComplex
      (constantLocalSystem (X := X) M)).d (n + 1) n ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  rw [localCoefficientChainComplex_d,
    constantCoefficientOrdinaryChainComplex_d]
  apply Finset.sum_congr rfl
  intro i _
  rw [constantLocalCoefficientFace]
  rfl

@[simp]
theorem constantLocalCoefficientChainIso_hom_f (n : ℕ) :
    (constantLocalCoefficientChainIso (X := X) M).hom.f n =
      (constantLocalCoefficientDegreeIso (X := X) M n).hom :=
  rfl

@[reassoc (attr := simp)]
theorem constantLocalCoefficientι_comp_chainIso_hom {n : ℕ}
    (σ : X _⦋n⦌) :
    constantLocalCoefficientι M σ ≫
        (constantLocalCoefficientChainIso (X := X) M).hom.f n =
      X.ιChainComplex σ := by
  rw [constantLocalCoefficientChainIso_hom_f]
  change Sigma.ι (fun _ : X _⦋n⦌ => M) σ ≫ 𝟙 _ =
    Sigma.ι (fun _ : X _⦋n⦌ => M) σ
  rw [Category.comp_id]

/-- Differential formula on a simplex summand for constant local
coefficients. -/
@[reassoc]
theorem constantLocalCoefficientι_d {n : ℕ} (σ : X _⦋n + 1⦌) :
    constantLocalCoefficientι M σ ≫
        (localCoefficientChainComplex
          (constantLocalSystem (X := X) M)).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        constantLocalCoefficientι M (X.δ i σ) := by
  rw [localCoefficientChainComplex_d, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.comp_zsmul]
  congr 1
  change nervePullbackCoefficientι (fundamentalGroupoidNerveUnit X)
      (constantLocalSystem (X := X) M) σ ≫
        nervePullbackCoefficientFace (fundamentalGroupoidNerveUnit X)
          (constantLocalSystem (X := X) M) i = _
  rw [nervePullbackCoefficientι_face,
    constantLocalCoefficientFaceHom]
  change 𝟙 M ≫ nervePullbackCoefficientι (fundamentalGroupoidNerveUnit X)
      (constantLocalSystem (X := X) M) (X.δ i σ) =
    nervePullbackCoefficientι (fundamentalGroupoidNerveUnit X)
      (constantLocalSystem (X := X) M) (X.δ i σ)
  rw [Category.id_comp]

/-- In degree one, the differential has signs `+,-` on the two faces. -/
theorem constantLocalCoefficientι_d_zero (σ : X _⦋1⦌) :
    constantLocalCoefficientι M σ ≫
        (localCoefficientChainComplex
          (constantLocalSystem (X := X) M)).d 1 0 =
      constantLocalCoefficientι M (X.δ 0 σ) -
        constantLocalCoefficientι M (X.δ 1 σ) := by
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using
    (constantLocalCoefficientι_d M (n := 0) σ)

/-- In degree two, the differential has signs `+,-,+` on the three faces. -/
theorem constantLocalCoefficientι_d_one (σ : X _⦋2⦌) :
    constantLocalCoefficientι M σ ≫
        (localCoefficientChainComplex
          (constantLocalSystem (X := X) M)).d 2 1 =
      constantLocalCoefficientι M (X.δ 0 σ) -
          constantLocalCoefficientι M (X.δ 1 σ) +
        constantLocalCoefficientι M (X.δ 2 σ) := by
  simpa [Fin.sum_univ_three, sub_eq_add_neg] using
    (constantLocalCoefficientι_d M (n := 1) σ)

end SSet
