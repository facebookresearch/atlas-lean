/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetConstant
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-! # Tests for constant local systems on simplicial sets -/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.SSetConstantTests

universe uR uX

section Generic

variable {R : Type uR} [CommRing R]
variable {X : SSet.{uX}}
variable (M : ModuleCat.{max uR uX} R)

example : SSet.LocalSystem R X := SSet.constantLocalSystem (X := X) M

example (n : ℕ) :
    SSet.localCoefficientFamily (SSet.constantLocalSystem (X := X) M) n =
      fun _ : X _⦋n⦌ => M :=
  SSet.constantLocalCoefficientFamily M n

example (n : ℕ) :
    SSet.localCoefficientObj (SSet.constantLocalSystem (X := X) M) n =
      ∐ fun _ : X _⦋n⦌ => M :=
  SSet.constantLocalCoefficientObj M n

example {n : ℕ} (σ : X _⦋n⦌) :
    SSet.constantLocalCoefficientι M σ =
      Sigma.ι (fun _ : X _⦋n⦌ => M) σ :=
  SSet.constantLocalCoefficientι_eq M σ

example {n : ℕ} (i : Fin (n + 2)) (σ : X _⦋n + 1⦌) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom
        (SSet.fundamentalGroupoidNerveUnit X)
        (SSet.constantLocalSystem (X := X) M) i σ = 𝟙 M :=
  SSet.constantLocalCoefficientFaceHom M i σ

example {n : ℕ} (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom
        (SSet.fundamentalGroupoidNerveUnit X)
        (SSet.constantLocalSystem (X := X) M) i σ = 𝟙 M :=
  SSet.constantLocalCoefficientDegeneracyHom M i σ

example {n : ℕ} (i : Fin (n + 2)) :
    SSet.localCoefficientFace (SSet.constantLocalSystem (X := X) M) i =
      Sigma.map' (fun σ : X _⦋n + 1⦌ => X.δ i σ) (fun _ => 𝟙 M) :=
  SSet.constantLocalCoefficientFace M i

example {n : ℕ} (i : Fin (n + 1)) :
    SSet.localCoefficientDegeneracy (SSet.constantLocalSystem (X := X) M) i =
      Sigma.map' (fun σ : X _⦋n⦌ => X.σ i σ) (fun _ => 𝟙 M) :=
  SSet.constantLocalCoefficientDegeneracy M i

example :
    SSet.localCoefficientChainComplex
        (SSet.constantLocalSystem (X := X) M) ≅
      X.chainComplex M :=
  SSet.constantLocalCoefficientChainIso (X := X) M

example (n : ℕ) :
    (SSet.constantLocalCoefficientChainIso (X := X) M).hom.f n =
      (SSet.constantLocalCoefficientDegreeIso (X := X) M n).hom :=
  SSet.constantLocalCoefficientChainIso_hom_f (X := X) M n

example {n : ℕ} (σ : X _⦋n⦌) :
    SSet.constantLocalCoefficientι M σ ≫
        (SSet.constantLocalCoefficientChainIso (X := X) M).hom.f n =
      X.ιChainComplex σ :=
  SSet.constantLocalCoefficientι_comp_chainIso_hom M σ

example {n : ℕ} (σ : X _⦋n + 1⦌) :
    SSet.constantLocalCoefficientι M σ ≫
        (SSet.localCoefficientChainComplex
          (SSet.constantLocalSystem (X := X) M)).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        SSet.constantLocalCoefficientι M (X.δ i σ) :=
  SSet.constantLocalCoefficientι_d M σ

example (σ : X _⦋1⦌) :
    SSet.constantLocalCoefficientι M σ ≫
        (SSet.localCoefficientChainComplex
          (SSet.constantLocalSystem (X := X) M)).d 1 0 =
      SSet.constantLocalCoefficientι M (X.δ 0 σ) -
        SSet.constantLocalCoefficientι M (X.δ 1 σ) :=
  SSet.constantLocalCoefficientι_d_zero M σ

example (σ : X _⦋2⦌) :
    SSet.constantLocalCoefficientι M σ ≫
        (SSet.localCoefficientChainComplex
          (SSet.constantLocalSystem (X := X) M)).d 2 1 =
      SSet.constantLocalCoefficientι M (X.δ 0 σ) -
          SSet.constantLocalCoefficientι M (X.δ 1 σ) +
        SSet.constantLocalCoefficientι M (X.δ 2 σ) :=
  SSet.constantLocalCoefficientι_d_one M σ

end Generic

section NonNerveSSet

variable {R : Type uR} [CommRing R]
variable (M : ModuleCat.{uR} R)

example :
    SSet.localCoefficientChainComplex
        (SSet.constantLocalSystem
          (X := (SSet.boundary 2 : SSet)) M) ≅
      (SSet.boundary 2 : SSet).chainComplex M :=
  SSet.constantLocalCoefficientChainIso
    (X := (SSet.boundary 2 : SSet)) M

end NonNerveSSet

section ZeroRing

example :
    SSet.localCoefficientChainComplex
        (SSet.constantLocalSystem
          (X := (SSet.boundary 2 : SSet))
          (ModuleCat.of (ZMod 1) (ZMod 1))) ≅
      (SSet.boundary 2 : SSet).chainComplex
        (ModuleCat.of (ZMod 1) (ZMod 1)) :=
  SSet.constantLocalCoefficientChainIso
    (X := (SSet.boundary 2 : SSet)) (ModuleCat.of (ZMod 1) (ZMod 1))

end ZeroRing

section RaisedUniverses

variable {R : Type 1} [CommRing R]
variable {X : SSet.{2}}
variable (M : ModuleCat.{2} R)

example :
    SSet.localCoefficientChainComplex
        (SSet.constantLocalSystem (X := X) M) ≅
      X.chainComplex M :=
  SSet.constantLocalCoefficientChainIso (X := X) M

end RaisedUniverses

#print axioms SSet.constantLocalSystem
#print axioms SSet.constantLocalCoefficientFamily
#print axioms SSet.constantLocalCoefficientObj
#print axioms SSet.constantLocalCoefficientι
#print axioms SSet.constantLocalCoefficientι_eq
#print axioms SSet.constantLocalCoefficientFaceHom
#print axioms SSet.constantLocalCoefficientDegeneracyHom
#print axioms SSet.constantLocalCoefficientFace
#print axioms SSet.constantLocalCoefficientDegeneracy
#print axioms SSet.constantCoefficientOrdinaryChainComplex_d
#print axioms SSet.constantLocalCoefficientDegreeIso
#print axioms SSet.constantLocalCoefficientChainIso
#print axioms SSet.constantLocalCoefficientChainIso_hom_f
#print axioms SSet.constantLocalCoefficientι_comp_chainIso_hom
#print axioms SSet.constantLocalCoefficientι_d
#print axioms SSet.constantLocalCoefficientι_d_zero
#print axioms SSet.constantLocalCoefficientι_d_one

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.SSetConstantTests
