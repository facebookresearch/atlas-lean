/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LambdaZeroHiggsComparison
public import MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry

/-!
# Actual relative framed lambda families

The base is an arbitrary complex scheme T. A family lives on the actual
product X×T with its projection to T, and its parameter is a section of O_T.
A frame is an isomorphism of the native restriction to {x}×T with O_T^n.
Family isomorphisms preserve the parameter, both connection operators,
and this actual frame. Base change is fixed by native pullback generators.

References: Carlos Simpson, alg-geom/9604005v1, Proposition 4.1 and section 4.
Ordinary products, module pullback, free modules and their coherence are
completed source integration from Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679
(Joël Riou, Andrew Yang), Apache 2.0. No representability, quotient, or
nonabelian-Hodge correspondence is assumed by these data.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
  AlgebraicGeometry.SheafedSpace.sheaf

namespace MathlibExt.AlgebraicGeometry.RelativeFramedLambdaFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open IntegrableHiggsBundles RelativeDifferentialForms RelativeDeRhamDifferential
open AlgebraicLambdaConnections RelativeLambdaReindexing
open LineBundleTaskContracts AlgebraicLineBundleFamilies CurveVectorBundles
open CoherentCurveLinearSeries

def projection (X T : ComplexScheme) : (prod X T).left ⟶ T.left :=
  (prod.snd : prod X T ⟶ T).left

def framingSection (X T : ComplexScheme) (x : 𝟙_ ComplexScheme ⟶ X) : T ⟶ prod X T :=
  prod.lift (toUnit T ≫ x) (𝟙 T)

def productMap (X : ComplexScheme) {S T : ComplexScheme} (f : S ⟶ T) : prod X S ⟶ prod X T :=
  prod.map (𝟙 X) f

theorem framing_square (X : ComplexScheme) {S T : ComplexScheme}
    (x : 𝟙_ ComplexScheme ⟶ X) (f : S ⟶ T) :
    framingSection X S x ≫ productMap X f = f ≫ framingSection X T x := by
  apply prod.hom_ext <;> simp [framingSection, productMap]

structure ProductBaseChange (X : ComplexScheme) {S T : ComplexScheme} (f : S ⟶ T) where
  square : RelativeSquare (projection X T) (projection X S)
  total_eq : square.total = (productMap X f).left
  base_eq : square.base = f.left

structure Family (X : ComplexScheme) (x : 𝟙_ ComplexScheme ⟶ X)
    (T : ComplexScheme) (D : Differential (projection X T)) (n : ℕ) where
  parameter : Γ(T.left, ⊤)
  connection : LambdaConnection (projection X T) parameter D
  rank_eq : connection.rank = n
  frame : (Scheme.Modules.pullback (framingSection X T x).left).obj connection.object ≅
    trivialBundle T.left n

namespace Family

variable {X T : ComplexScheme} {x : 𝟙_ ComplexScheme ⟶ X}
  {D : Differential (projection X T)} {n : ℕ}

structure Iso (E F : Family X x T D n) where
  parameter_eq : E.parameter = F.parameter
  bundle : E.connection.object ≅ F.connection.object
  operator0 : ∀ (U : (prod X T).left.Opens) (s : E.connection.object.val.obj (op U)),
    ((tensorMap bundle.hom (𝟙 (forms (projection X T) 1))).val.app (op U)).hom
      (E.connection.nabla0 U s) = F.connection.nabla0 U ((bundle.hom.val.app (op U)).hom s)
  operator1 : ∀ (U : (prod X T).left.Opens)
      (s : (moduleTensor (prod X T).left E.connection.object (forms (projection X T) 1)).val.obj
        (op U)),
    ((tensorMap bundle.hom (𝟙 (forms (projection X T) 2))).val.app (op U)).hom
      (E.connection.nabla1 U s) = F.connection.nabla1 U
        (((tensorMap bundle.hom (𝟙 (forms (projection X T) 1))).val.app (op U)).hom s)
  frame_eq : (Scheme.Modules.pullback (framingSection X T x).left).map bundle.hom ≫
    F.frame.hom = E.frame.hom

def changeFrame (E : Family X x T D n) (g : Aut (trivialBundle T.left n)) :
    Family X x T D n := { E with frame := E.frame ≪≫ g.asIso }

@[simp] theorem changeFrame_parameter (E : Family X x T D n) (g : Aut (trivialBundle T.left n)) :
    (changeFrame E g).parameter = E.parameter := rfl

@[simp] theorem changeFrame_connection (E : Family X x T D n) (g : Aut (trivialBundle T.left n)) :
    (changeFrame E g).connection = E.connection := rfl

def scale (E : Family X x T D n) (a : Γ(T.left, ⊤)) : Family X x T D n where
  parameter := a * E.parameter
  connection := LambdaConnectionScaling.scale a E.connection
  rank_eq := E.rank_eq
  frame := E.frame

end Family

variable {n : ℕ}

structure FreePullbackComparison {S T : ComplexScheme} (f : S ⟶ T) (n : ℕ) where
  iso : (Scheme.Modules.pullback f.left).obj (trivialBundle T.left n) ≅ trivialBundle S.left n
  generators : ∀ i : Fin n,
    (Scheme.Modules.pullback f.left).map (Sigma.ι (fun _ : Fin n ↦ structureModule T.left) i) ≫
      iso.hom = (AlgebraicBundleGeometry.pullbackUnit S.left T.left f.left).hom ≫
        Sigma.ι (fun _ : Fin n ↦ structureModule S.left) i

def pulledFrame (X : ComplexScheme) {S T : ComplexScheme} (x : 𝟙_ ComplexScheme ⟶ X)
    (f : S ⟶ T) (Q : ProductBaseChange X f) (I : FreePullbackComparison f n)
    {D : Differential (projection X T)} (E : Family X x T D n) :
    (Scheme.Modules.pullback (framingSection X S x).left).obj
      ((Scheme.Modules.pullback Q.square.total).obj E.connection.object) ⟶
        trivialBundle S.left n :=
  (Scheme.Modules.pullbackComp (framingSection X S x).left Q.square.total).hom.app
      E.connection.object ≫
    (Scheme.Modules.pullbackCongr (by
      rw [Q.total_eq]
      exact congrArg (fun g : S ⟶ prod X T ↦ g.left) (framing_square X x f))).hom.app
        E.connection.object ≫
    (Scheme.Modules.pullbackComp f.left (framingSection X T x).left).inv.app E.connection.object ≫
    (Scheme.Modules.pullback f.left).map E.frame.hom ≫ I.iso.hom

structure PulledFamily (X : ComplexScheme) {S T : ComplexScheme}
    (x : 𝟙_ ComplexScheme ⟶ X) (f : S ⟶ T) (Q : ProductBaseChange X f)
    (C : TensorPullbackComparison Q.square.total) (I : FreePullbackComparison f n)
    {D : Differential (projection X T)} {D' : Differential (projection X S)}
    (F : FormBaseChange Q.square C D D') (E : Family X x T D n) where
  pull : PulledConnection Q.square C F E.connection
  frame : (Scheme.Modules.pullback (framingSection X S x).left).obj pull.connection.object ≅
    trivialBundle S.left n
  frame_normalization :
    (Scheme.Modules.pullback (framingSection X S x).left).map pull.bundleIso.hom ≫ frame.hom =
      pulledFrame X x f Q I E

def PulledFamily.family (X : ComplexScheme) {S T : ComplexScheme}
    (x : 𝟙_ ComplexScheme ⟶ X) (f : S ⟶ T) (Q : ProductBaseChange X f)
    (C : TensorPullbackComparison Q.square.total) (I : FreePullbackComparison f n)
    {D : Differential (projection X T)} {D' : Differential (projection X S)}
    (F : FormBaseChange Q.square C D D') (E : Family X x T D n)
    (P : PulledFamily X x f Q C I F E) : Family X x S D' n where
  parameter := Q.square.parameter E.parameter
  connection := P.pull.connection
  rank_eq := P.pull.rank_eq.trans E.rank_eq
  frame := P.frame

end MathlibExt.AlgebraicGeometry.RelativeFramedLambdaFamilies
