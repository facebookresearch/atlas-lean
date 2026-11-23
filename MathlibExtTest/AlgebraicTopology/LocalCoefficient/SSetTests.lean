/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSet
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Tests for simplicial-set local-coefficient chains

These clients pin the canonical fundamental-groupoid nerve unit, including
its forward-edge orientation, and the object, face, degeneracy, and
unnormalized differential formulas for local coefficients.  Point,
one-object, zero-ring, and independent-universe cases exercise the intended
boundary without claiming functoriality, homology, or a constant comparison.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

universe uR uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.SSetTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X : SSet.{uX}}
variable (L : SSet.LocalSystem R X)

example : X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid X) :=
  SSet.fundamentalGroupoidNerveUnit X

example (x : X _⦋0⦌) :
    (SSet.fundamentalGroupoidNerveUnit X).app _ x =
      CategoryTheory.nerveEquiv.symm
        (SSet.FundamentalGroupoid.mk x) :=
  SSet.fundamentalGroupoidNerveUnit_app_zero X x

example {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (SSet.fundamentalGroupoidNerveUnit X).app _ e.edge =
      ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk e) :=
  SSet.fundamentalGroupoidNerveUnit_app_edge X e

section EdgeFaces

private theorem normalize_face_zero
    {a b : SSet.FundamentalGroupoid X}
    (g : a ⟶ b)
    (F : ComposableArrows (SSet.FundamentalGroupoid X) 1)
    (V : ComposableArrows (SSet.FundamentalGroupoid X) 0)
    (hF : F = ComposableArrows.mk₁ g)
    (hV : V = CategoryTheory.nerveEquiv.symm b)
    (hidx : (CategoryTheory.nerve (SSet.FundamentalGroupoid X)).δ 0 F = V) :
    eqToHom (congrArg (fun K => L.obj K.left) hF).symm ≫
        (coefficientFaceHom L (0 : Fin 2) F ≫
          eqToHom (congrArg (fun K => L.obj K.left) hidx)) =
      L.map g ≫
        eqToHom (congrArg (fun K => L.obj K.left) hV.symm) := by
  subst F
  subst V
  change eqToHom _ ≫ L.map g ≫ eqToHom _ =
    L.map g ≫ eqToHom _
  cat_disch

private theorem normalize_face_one
    {a b : SSet.FundamentalGroupoid X}
    (g : a ⟶ b)
    (F : ComposableArrows (SSet.FundamentalGroupoid X) 1)
    (V : ComposableArrows (SSet.FundamentalGroupoid X) 0)
    (hF : F = ComposableArrows.mk₁ g)
    (hV : V = CategoryTheory.nerveEquiv.symm a)
    (hidx : (CategoryTheory.nerve (SSet.FundamentalGroupoid X)).δ 1 F = V) :
    eqToHom (congrArg (fun K => L.obj K.left) hF).symm ≫
        (coefficientFaceHom L (1 : Fin 2) F ≫
          eqToHom (congrArg (fun K => L.obj K.left) hidx)) =
      eqToHom (congrArg (fun K => L.obj K.left) hV.symm) := by
  subst F
  subst V
  change eqToHom _ ≫ L.map (𝟙 a) ≫ eqToHom _ = eqToHom _
  rw [L.map_id]
  cat_disch

variable {x y : X _⦋0⦌} (e : SSet.Edge x y)

private theorem unit_edge_eq :
    (SSet.fundamentalGroupoidNerveUnit X).app _ e.edge =
      ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk e) :=
  SSet.fundamentalGroupoidNerveUnit_app_edge X e

private theorem unit_target_eq :
    (SSet.fundamentalGroupoidNerveUnit X).app _ (X.δ 0 e.edge) =
      CategoryTheory.nerveEquiv.symm
        (SSet.FundamentalGroupoid.mk y) := by
  rw [SSet.fundamentalGroupoidNerveUnit_app_zero, e.tgt_eq]

private theorem unit_source_eq :
    (SSet.fundamentalGroupoidNerveUnit X).app _ (X.δ 1 e.edge) =
      CategoryTheory.nerveEquiv.symm
        (SSet.FundamentalGroupoid.mk x) := by
  rw [SSet.fundamentalGroupoidNerveUnit_app_zero, e.src_eq]

-- The zeroth component is the forward local-system action, followed only by
-- the canonical target transport.
example :
    eqToHom (congrArg (fun K => L.obj K.left) (unit_edge_eq e)).symm ≫
        nervePullbackCoefficientFaceHom
          (SSet.fundamentalGroupoidNerveUnit X) L
            (0 : Fin 2) e.edge =
      L.map (SSet.FundamentalGroupoid.homMk e) ≫
        eqToHom (congrArg (fun K => L.obj K.left)
          (unit_target_eq e).symm) := by
  exact normalize_face_zero L _ _ _ (unit_edge_eq e) (unit_target_eq e)
    (nervePullback_face_index
      (SSet.fundamentalGroupoidNerveUnit X) 0 e.edge)

-- The other component preserves the initial coefficient by identity
-- transport; no inverse edge action occurs.
example :
    eqToHom (congrArg (fun K => L.obj K.left) (unit_edge_eq e)).symm ≫
        nervePullbackCoefficientFaceHom
          (SSet.fundamentalGroupoidNerveUnit X) L
            (1 : Fin 2) e.edge =
      eqToHom (congrArg (fun K => L.obj K.left)
        (unit_source_eq e).symm) := by
  exact normalize_face_one L _ _ _ (unit_edge_eq e) (unit_source_eq e)
    (nervePullback_face_index
      (SSet.fundamentalGroupoidNerveUnit X) 1 e.edge)

-- Both actual degree-one face maps are exercised through their coproduct
-- summand formulas.
example :
    nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit X) L e.edge ≫
      SSet.localCoefficientFace L (0 : Fin 2) =
    nervePullbackCoefficientFaceHom
        (SSet.fundamentalGroupoidNerveUnit X) L 0 e.edge ≫
      nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit X) L (X.δ 0 e.edge) :=
  nervePullbackCoefficientι_face
    (SSet.fundamentalGroupoidNerveUnit X) L 0 e.edge

example :
    nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit X) L e.edge ≫
      SSet.localCoefficientFace L (1 : Fin 2) =
    nervePullbackCoefficientFaceHom
        (SSet.fundamentalGroupoidNerveUnit X) L 1 e.edge ≫
      nervePullbackCoefficientι
        (SSet.fundamentalGroupoidNerveUnit X) L (X.δ 1 e.edge) :=
  nervePullbackCoefficientι_face
    (SSet.fundamentalGroupoidNerveUnit X) L 1 e.edge

end EdgeFaces

example (n : ℕ) : X _⦋n⦌ → ModuleCat.{max uR uX} R :=
  SSet.localCoefficientFamily L n

example (x : X _⦋0⦌) :
    SSet.localCoefficientFamily L 0 x =
      L.obj (SSet.FundamentalGroupoid.mk x) :=
  SSet.localCoefficientFamily_zero L x

example (n : ℕ) : ModuleCat.{max uR uX} R :=
  SSet.localCoefficientObj L n

example : SimplicialObject (ModuleCat.{max uR uX} R) :=
  SSet.localCoefficientSimplicial L

example (n : ℕ) :
    (SSet.localCoefficientSimplicial L).obj
        (op (SimplexCategory.mk n)) =
      SSet.localCoefficientObj L n :=
  SSet.localCoefficientSimplicial_obj L n

example {n : ℕ} (i : Fin (n + 2)) :
    (SSet.localCoefficientSimplicial L).map
        (SimplexCategory.δ i).op =
      SSet.localCoefficientFace L i :=
  SSet.localCoefficientSimplicial_map_δ L i

example {n : ℕ} (i : Fin (n + 1)) :
    (SSet.localCoefficientSimplicial L).map
        (SimplexCategory.σ i).op =
      SSet.localCoefficientDegeneracy L i :=
  SSet.localCoefficientSimplicial_map_σ L i

example : ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
  SSet.localCoefficientChainComplex L

example (n : ℕ) :
    (SSet.localCoefficientChainComplex L).X n =
      SSet.localCoefficientObj L n :=
  SSet.localCoefficientChainComplex_X L n

example (n : ℕ) :
    (SSet.localCoefficientChainComplex L).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        SSet.localCoefficientFace L i :=
  SSet.localCoefficientChainComplex_d L n

end Generic

section Point

variable {R : Type uR} [CommRing R]
variable (L : SSet.LocalSystem R Δ[0])

example : SimplicialObject (ModuleCat.{uR} R) :=
  SSet.localCoefficientSimplicial L

example : ChainComplex (ModuleCat.{uR} R) ℕ :=
  SSet.localCoefficientChainComplex L

example (x : Δ[0] _⦋0⦌) :
    SSet.localCoefficientFamily L 0 x =
      L.obj (SSet.FundamentalGroupoid.mk x) :=
  SSet.localCoefficientFamily_zero L x

end Point

section OneObject

private def swap₂ : Equiv.Perm (Fin 2) := Equiv.swap 0 1

private def swapEnd :
    End (SingleObj.star (Equiv.Perm (Fin 2))) :=
  SingleObj.toEnd (Equiv.Perm (Fin 2)) swap₂

example : swap₂ ≠ 1 := by decide

example :
    (SSet.fundamentalGroupoidNerveUnit
        (CategoryTheory.nerve (SingleObj (Equiv.Perm (Fin 2))))).app _
          (CategoryTheory.nerve.edgeMk swapEnd.asHom).edge =
      ComposableArrows.mk₁
        (SSet.FundamentalGroupoid.homMk
          (CategoryTheory.nerve.edgeMk swapEnd.asHom)) :=
  SSet.fundamentalGroupoidNerveUnit_app_edge _ _

variable (L : SSet.LocalSystem (ZMod 1)
  (CategoryTheory.nerve (SingleObj (Equiv.Perm (Fin 2)))))

example : SimplicialObject (ModuleCat (ZMod 1)) :=
  SSet.localCoefficientSimplicial L

example : ChainComplex (ModuleCat (ZMod 1)) ℕ :=
  SSet.localCoefficientChainComplex L

end OneObject

section RaisedSimplexUniverse

variable (R : Type 1) [CommRing R]
variable (X : SSet.{2})
variable (L : SSet.LocalSystem R X)

example : SimplicialObject (ModuleCat.{2} R) :=
  SSet.localCoefficientSimplicial L

example : ChainComplex (ModuleCat.{2} R) ℕ :=
  SSet.localCoefficientChainComplex L

end RaisedSimplexUniverse

section RaisedRingUniverse

variable (R : Type 2) [CommRing R]
variable (X : SSet.{1})
variable (L : SSet.LocalSystem R X)

example : SimplicialObject (ModuleCat.{2} R) :=
  SSet.localCoefficientSimplicial L

example : ChainComplex (ModuleCat.{2} R) ℕ :=
  SSet.localCoefficientChainComplex L

end RaisedRingUniverse

section StoppingBoundary

-- Local-system natural-transformation functoriality is a later packet.
#guard_msgs (error, substring := true) in
#check SSet.localCoefficientMap

-- Homology is outside this packet.
#guard_msgs (error, substring := true) in
#check SSet.localCoefficientHomology

end StoppingBoundary

#print axioms SSet.fundamentalGroupoidNerveUnit
#print axioms SSet.fundamentalGroupoidNerveUnit_app_zero
#print axioms SSet.fundamentalGroupoidNerveUnit_app_edge
#print axioms SSet.localCoefficientFamily_zero
#print axioms SSet.localCoefficientSimplicial
#print axioms SSet.localCoefficientSimplicial_obj
#print axioms SSet.localCoefficientSimplicial_map_δ
#print axioms SSet.localCoefficientSimplicial_map_σ
#print axioms SSet.localCoefficientChainComplex
#print axioms SSet.localCoefficientChainComplex_X
#print axioms SSet.localCoefficientChainComplex_d

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.SSetTests
