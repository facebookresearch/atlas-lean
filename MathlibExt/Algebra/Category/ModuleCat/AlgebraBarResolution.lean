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

public import MathlibExt.Algebra.Category.ModuleCat.AlgebraTensorAdjunction
public import MathlibExt.CategoryTheory.Monad.AdjunctionBarContraction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# The adjunction Bar resolution over an associative algebra

Let R be a commutative ring, A an associative unital R-algebra, and
H = max(u,v,w) a common module height. Scalar extension
F(X) = A ⊗[R] X is left adjoint to restriction G along R → A.
For an A-module Y at height H, its augmented simplicial Bar has degree-n
object F((GF)^n(GY)), with faces induced by algebra multiplication
and the module action. Its degree-zero augmentation is
a ⊗ y ↦ a • y.

The alternating-face complex has the full signed sum of these faces
as differential. After restriction to R, the adjunction unit supplies
an extra degeneracy, with augmentation section y ↦ 1 ⊗ y.
Thus the Bar augmentation is a quasi-isomorphism for every Y.

If A and the restricted module GY are free over R, every Bar term is
projective over A. The complex and its augmentation then give a
projective resolution of Y. The worlds u and v of R and A and the
additional module height w are independent, and A may be noncommutative.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Monad AlgebraicTopology Opposite
open scoped TensorProduct ModuleCat.Algebra Simplicial

namespace ModuleCat.AlgebraBar

variable (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A]


/-- For a commutative ring R, an associative unital R-algebra A
and Y ∈ ModuleCat^H(A), with H = max(u,v,w), the adjunction
F = A ⊗[R] − ⊣ G = restriction gives an augmented simplicial
A-module with degree-n term F((GF)^n(GY)) and augmentation target Y.
The augmentation in degree zero is the adjunction counit. -/
def augmented (Y : (ModuleCat.{max u v w} A)) : SimplicialObject.Augmented (ModuleCat.{max u v w} A) :=
  (SimplicialObject.Augmented.whiskeringObj
    (ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} A) (ModuleCat.{max u v w} A)
    ((evaluation (ModuleCat.{max u v w} A) (ModuleCat.{max u v w} A)).obj Y)).obj
    (Monad.adjAugmented (AlgebraTensor.adjunction.{u, v, w} R A))

@[simp]
theorem augmented_point (Y : (ModuleCat.{max u v w} A)) : (augmented R A Y).right = Y := rfl

/-- For a commutative ring R, an associative unital R-algebra A
and an A-module Y at height H = max(u,v,w), the Bar chain complex
is the alternating-face complex of its augmented simplicial object.
Its differential from degree n+1 to n is
∑_(i=0)^(n+1) (−1)^i δ_i, with the algebra and module-action faces. -/
def complex (Y : (ModuleCat.{max u v w} A)) : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  AlternatingFaceMapComplex.obj (augmented R A Y).left

/-- For a commutative ring R, an associative unital R-algebra A
and an A-module Y, the Bar augmentation is the chain map from the
alternating-face complex to Y concentrated in degree zero.
Its degree-zero component is a ⊗ y ↦ a • y, and its positive
degree components have zero target. -/
def augmentation (Y : ModuleCat.{max u v w} A) :
    complex R A Y ⟶ (ChainComplex.single₀ (ModuleCat.{max u v w} A)).obj Y :=
  AlternatingFaceMapComplex.ε.app (augmented R A Y)

@[simp]
theorem augmentation_f_zero (Y : (ModuleCat.{max u v w} A)) :
    (augmentation R A Y).f 0 = (AlgebraTensor.adjunction.{u, v, w} R A).counit.app Y := by
  rw [augmentation, AlternatingFaceMapComplex.ε_app_f_zero]
  unfold augmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    Monad.adjAugmented_hom_zero]
  rfl

/-- For a commutative ring R, an associative unital R-algebra A,
Y ∈ ModuleCat^H(A) and n ≥ 0, the degree-n Bar object is
F((GF)^n(GY)), where F(X) = A ⊗[R] X and G restricts scalars.
This description holds for arbitrary Y, without a freeness
assumption on its ground module. -/
theorem complex_X (Y : (ModuleCat.{max u v w} A)) (n : ℕ) :
    (complex R A Y).X n = (AlgebraTensor.functor.{u, v, w} R A).obj
      ((Monad.monadPow (AlgebraTensor.adjunction.{u, v, w} R A).toMonad n).obj
        ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y)) := rfl

/-- For a commutative ring R, an associative unital R-algebra A
and an A-module Y, restricting its augmented simplicial Bar along
R → A gives an augmented R-module simplicial object.
Its target is GY and its degree-n object is G(F((GF)^n(GY))). -/
def forgotten (Y : (ModuleCat.{max u v w} A)) : SimplicialObject.Augmented (ModuleCat.{max u v w} R) :=
  (SimplicialObject.Augmented.whiskeringObj (ModuleCat.{max u v w} A) (ModuleCat.{max u v w} R)
    (ModuleCat.restrictScalars.{max u v w} (algebraMap R A))).obj (augmented R A Y)

/-- For a commutative ring R, an associative unital R-algebra A
and an A-module Y, the restricted augmented Bar has the extra
degeneracy of the adjunction unit. Its augmentation section is
GY → GFGY, y ↦ 1 ⊗ y.
The extra-degeneracy identities give a homotopy equivalence from
the restricted alternating-face complex to GY in degree zero. -/
def forgottenExtra (Y : (ModuleCat.{max u v w} A)) : (forgotten R A Y).ExtraDegeneracy := by
  change (Monad.AdjunctionBarContraction.forgotten (AlgebraTensor.adjunction.{u, v, w} R A) Y).ExtraDegeneracy
  exact Monad.AdjunctionBarContraction.extra (AlgebraTensor.adjunction.{u, v, w} R A) Y

/-- For a commutative ring R, an associative unital R-algebra A
and an A-module Y, restriction of its Bar chain complex is
isomorphic to the alternating-face complex of the restricted
simplicial Bar. Both complexes have terms G(F((GF)^n(GY))) and
differentials given by restriction of the signed face sums. -/
def forgottenComplexIso (Y : (ModuleCat.{max u v w} A)) :
    ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (complex R A Y) ≅
      AlternatingFaceMapComplex.obj (forgotten R A Y).left :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
    (ModuleCat.restrictScalars.{max u v w} (algebraMap R A))).app (augmented R A Y).left

/-- For an R-algebra A and an A-module Y, let G restrict
scalars, α identify G(Bar_*(Y)) with the restricted Bar's
alternating-face complex, and χ identify G(Y[0]) with (GY)[0].
The augmentations satisfy χ ∘ G(ε) = ε_forgot ∘ α.
This is a square of R-module chain complexes at height max(u,v,w). -/
theorem forgottenAugmentation_square (Y : (ModuleCat.{max u v w} A)) :
    ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (augmentation R A Y) ≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars.{max u v w} (algebraMap R A))
        (ComplexShape.down ℕ) 0).app Y).hom =
        (forgottenComplexIso R A Y).hom ≫
          AlternatingFaceMapComplex.ε.app (forgotten R A Y) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      let G : ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} R :=
        ModuleCat.restrictScalars (algebraMap R A)
      change G.map ((augmented R A Y).hom.app (op ⦋0⦌)) ≫ 𝟙 _ =
        𝟙 _ ≫ G.map ((augmented R A Y).hom.app (op ⦋0⦌))
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
        ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y)
        (n + 1) (by omega)).eq_of_tgt _ _

local instance restriction_preservesHomology :
    (ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).PreservesHomology :=
  Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{max u v w} (algebraMap R A))

/-- For a commutative ring R, an associative unital R-algebra A
and any A-module Y at height max(u,v,w), the augmentation
Bar_*(Y) → Y[0] is a quasi-isomorphism.
It identifies degree-zero homology with Y and has zero homology
in every positive degree. -/
theorem augmentation_quasiIso (Y : (ModuleCat.{max u v w} A)) : QuasiIso (augmentation R A Y) := by
  have hε : QuasiIso (AlternatingFaceMapComplex.ε.app (forgotten R A Y)) :=
    (forgottenExtra R A Y).homotopyEquiv.quasiIso_hom
  let e := (HomologicalComplex.singleMapHomologicalComplex
    (ModuleCat.restrictScalars.{max u v w} (algebraMap R A)) (ComplexShape.down ℕ) 0).app Y
  letI : QuasiIso (((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map
      (augmentation R A Y) ≫ e.hom) := by
    rw [forgottenAugmentation_square]
    exact quasiIso_comp
      (hφ := quasiIso_of_isIso ((forgottenComplexIso R A Y).hom)) (hφ' := hε) _ _
  have hmap : QuasiIso (((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map
      (augmentation R A Y)) :=
    quasiIso_of_comp_right (hφ := quasiIso_of_isIso e.hom) _ e.hom
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (augmentation R A Y) (ModuleCat.restrictScalars.{max u v w} (algebraMap R A))).mp hmap

/-- For a commutative ring R and an associative unital
R-algebra A free as an R-module, let F = A ⊗[R] − and G be
restriction. If X is an R-free module, then (GF)^n(X) is R-free
for every n ≥ 0. The modules lie at height max(u,v,w). -/
theorem monadPow_moduleFree [Module.Free R A] (X : (ModuleCat.{max u v w} R)) [Module.Free R X] (n : ℕ) :
    Module.Free R ((Monad.monadPow (AlgebraTensor.adjunction.{u, v, w} R A).toMonad n).obj X) := by
  induction n with
  | zero =>
      change Module.Free R X
      infer_instance
  | succ n ih =>
      rw [Monad.monadPow_succ_obj_eq]
      letI : Module.Free R ((Monad.monadPow (AlgebraTensor.adjunction.{u, v, w} R A).toMonad n).obj X) := ih
      exact AlgebraTensor.groundObj_moduleFree R A
        ((Monad.monadPow (AlgebraTensor.adjunction.{u, v, w} R A).toMonad n).obj X)

/-- For a commutative ring R and an associative unital
R-algebra A, assume A and GY are free over R, where Y is an
A-module and G restricts scalars. Then the degree-n Bar object
F((GF)^n(GY)) is a projective A-module for every n ≥ 0. -/
instance complex_projective [Module.Free R A] (Y : ModuleCat.{max u v w} A)
    [Module.Free R ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y)] (n : ℕ) :
    Projective ((complex R A Y).X n) := by
  rw [complex_X]
  letI : Module.Free R ((Monad.monadPow (AlgebraTensor.adjunction.{u, v, w} R A).toMonad n).obj
    ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y)) :=
    monadPow_moduleFree R A ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y) n
  exact AlgebraTensor.obj_projective R A _

/-- For a commutative ring R and an associative unital
R-algebra A, if A and the restricted A-module GY are free over R,
the alternating-face Bar complex with its counit augmentation
is a projective resolution of Y in ModuleCat^max(u,v,w)(A).
The augmentation and projectivity are those of the stated Bar terms. -/
def projectiveResolution [Module.Free R A] (Y : ModuleCat.{max u v w} A)
    [Module.Free R ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y)] :
    ProjectiveResolution Y where
  complex := complex R A Y
  projective := fun n => inferInstance
  π := augmentation R A Y
  quasiIso := augmentation_quasiIso R A Y

end ModuleCat.AlgebraBar
