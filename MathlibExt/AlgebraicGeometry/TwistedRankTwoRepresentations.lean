/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RankTwoMatrixGroupModels
public import MathlibExt.AlgebraicGeometry.LinearizedLineBundles

/-!
# The actual twisted rank-two representation scheme

The parameter scheme is the native finite product of GL2 schemes. Its
word map is the actual product A_i^-1 B_i^-1 A_i B_i, in source order.
The representation scheme is its literal fibre over the scalar matrix
-I. Its test objects are matrices over the actual global-function ring
of every complex coefficient scheme, including nonreduced schemes.
Conjugation is bound to the actual generator projection maps.
Source: de Cataldo--Hausel--Migliorini arXiv:1004.1420v2,
Introduction and Section1.2.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.TwistedRankTwoRepresentations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels

variable [F : FrameTheory 2] [M : GL2MatrixTheory]

abbrev Generators (g : ℕ) := Fin g × Fin 2

def parameters (g : ℕ) : Over (Spec (.of ℂ)) :=
  ∏ᶜ fun _ : Generators g => frameScheme 2

def generator (g : ℕ) (i : Generators g) : parameters g ⟶ frameScheme 2 :=
  Pi.π (fun _ : Generators g => frameScheme 2) i

def multiplyMaps {U : Over (Spec (.of ℂ))} (f h : U ⟶ frameScheme 2) : U ⟶ frameScheme 2 :=
  CartesianMonoidalCategory.lift f h ≫ μ[frameScheme 2]

def commutator {U : Over (Spec (.of ℂ))} (a b : U ⟶ frameScheme 2) : U ⟶ frameScheme 2 :=
  multiplyMaps (multiplyMaps (multiplyMaps (a ≫ ι[frameScheme 2])
    (b ≫ ι[frameScheme 2])) a) b

def conjugate {U : Over (Spec (.of ℂ))} (a b : U ⟶ frameScheme 2) : U ⟶ frameScheme 2 :=
  multiplyMaps (multiplyMaps a b) (a ≫ ι[frameScheme 2])

def productMaps {U : Over (Spec (.of ℂ))} (fs : List (U ⟶ frameScheme 2)) : U ⟶ frameScheme 2 :=
  fs.foldl multiplyMaps (toUnit U ≫ η[frameScheme 2])

def word (g : ℕ) : parameters g ⟶ frameScheme 2 :=
  productMaps ((List.finRange g).map fun i => commutator (generator g (i, 0)) (generator g (i, 1)))

def representation (g : ℕ) : Over (Spec (.of ℂ)) := pullback (word g) minusPoint

def ambient (g : ℕ) : representation g ⟶ parameters g := pullback.fst (word g) minusPoint

def matrixGenerator (g : ℕ) (i : Generators g) : representation g ⟶ frameScheme 2 :=
  ambient g ≫ generator g i

theorem word_relation (g : ℕ) :
    ambient g ≫ word g = pullback.snd (word g) minusPoint ≫ minusPoint :=
  pullback.condition

def matrixWord {R : Type} [CommRing R] {g : ℕ}
    (m : Generators g → Matrix.GeneralLinearGroup (Fin 2) R) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  (List.finRange g).foldl (fun acc i => acc *
    (m (i, 0))⁻¹ * (m (i, 1))⁻¹ * m (i, 0) * m (i, 1)) 1

def Points (g : ℕ) (U : Over (Spec (.of ℂ))) :=
  {m : Generators g → Matrix.GeneralLinearGroup (Fin 2) Γ(U.left, ⊤) //
    matrixWord m = minusGL Γ(U.left, ⊤)}

structure PointModel (g : ℕ) where
  points : ∀ U : Over (Spec (.of ℂ)), (U ⟶ representation g) ≃ Points g U
  generators : ∀ (U : Over (Spec (.of ℂ))) (f : U ⟶ representation g) (i : Generators g),
    (points U f).val i = M.points U (f ≫ matrixGenerator g i)
  naturality : ∀ {U U' : Over (Spec (.of ℂ))} (h : U' ⟶ U)
      (f : U ⟶ representation g) (i : Generators g),
    (points U' (h ≫ f)).val i =
      Matrix.GeneralLinearGroup.map h.left.appTop.hom ((points U f).val i)

class Conjugation (g : ℕ) where
  [action : ModObj (frameScheme 2) (representation g)]
  generators : ∀ i : Generators g,
    γ[frameScheme 2,representation g] ≫ matrixGenerator g i =
      conjugate (fst (frameScheme 2) (representation g))
        (snd (frameScheme 2) (representation g) ≫ matrixGenerator g i)

attribute [instance_reducible, instance] Conjugation.action

end MathlibExt.AlgebraicGeometry.TwistedRankTwoRepresentations
