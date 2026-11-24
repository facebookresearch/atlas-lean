/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialSet/Pointed/ReducedFree.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Smash.Basic
public import MathlibExt.AlgebraicTopology.SpectraSource.LinearAlgebra.Finsupp.ReducedFree

/-!
# The reduced free module on a pointed simplicial set

For a ring `R` and a pointed simplicial set `X`, the reduced free module `R~[X]` has as
`n`-simplices the reduced free `R`-module on the pointed set `X_n`: the free module on `X_n`
modulo the generator of the basepoint. Simplicial operators act on generators, and the basepoint
is zero. This is the functor `PointedSSet.reducedFree R`, and the generators give the based map
`PointedSSet.reducedFreeι R X : X ⟶ R~[X]`, natural in `X` (`PointedSSet.toReducedFree R`).

For a commutative ring `R`, the external product of generators `[x] ∧ [y] ↦ [x ∧ y]` extends
bilinearly to based maps `R~[X] ∧ R~[Y] ⟶ R~[X ∧ Y]`. With the unit `S⁰ ⟶ R~[S⁰]` given by the
generators, they make `R~[-]` a lax braided functor on pointed simplicial sets with the smash
product, and `X ⟶ R~[X]` a monoidal natural transformation. Applied to the spheres
`Sⁿ = (S¹)^∧n`, this gives the commutative ring structure of the Eilenberg–MacLane symmetric
spectrum `HR`, with levels `R~[Sⁿ]`, and its unit map from the sphere spectrum.

For an `R`-module `M`, the reduced free module with coefficients in `M` is
`M~[X] = R~[X] ⊗_R M`, whose `n`-simplices are the finite formal sums `Σ xᵢ ⊗ mᵢ` of `n`-simplices
of `X` with coefficients in `M`, modulo the basepoint (`PointedSSet.reducedFreeTensor R M`). The
bilinear extension of `[x] ∧ ([y] ⊗ m) ↦ [x ∧ y] ⊗ m` is an action
`R~[X] ∧ M~[Y] ⟶ M~[X ∧ Y]` of the lax monoidal functor `R~[-]` on `M~[-]`, natural, unital and
associative. Along a lax monoidal functor `K` to pointed simplicial sets, followed by the
  tensorator
of `K`, it gives structure maps `R~[K p] ∧ M~[K q] ⟶ M~[K (p ⊗ q)]` satisfying the module laws over
`K ⋙ R~[-]`. Applied to the spheres, these are the levels and structure maps of the
Eilenberg–MacLane spectrum `HM` as a module over `HR`. A linear map `M ⟶ N` changes the
coefficients compatibly with the action.

## Main definitions

* `PointedSSet.reducedFree R`: the reduced free `R`-module functor `X ↦ R~[X]`.
* `PointedSSet.reducedFreeι R X`: the based map `X ⟶ R~[X]` sending a simplex to its generator,
  and `PointedSSet.toReducedFree R`: the corresponding natural transformation.
* `PointedSSet.reducedFreeμ R X Y`: the external product `R~[X] ∧ R~[Y] ⟶ R~[X ∧ Y]`.
* `PointedSSet.reducedFreeTensor R M`: the reduced free module functor `X ↦ M~[X]` with
  coefficients in an `R`-module `M`.
* `PointedSSet.reducedFreeTensorAct R M X Y`: the action `R~[X] ∧ M~[Y] ⟶ M~[X ∧ Y]`.
* `PointedSSet.reducedFreeTensorMap R g`: the change of coefficients `M~[X] ⟶ N~[X]` along a
  linear map `g : M →ₗ[R] N`.
* `PointedSSet.reducedFreeTensorCompAct R M K`: the action along a lax monoidal functor `K`,
  `R~[K p] ∧ M~[K q] ⟶ M~[K (p ⊗ q)]`.

## Main statements

* The instance `(PointedSSet.reducedFree R).LaxBraided`, and the instance stating that
  `PointedSSet.toReducedFree R` is a monoidal natural transformation.
* `PointedSSet.reducedFreeTensorAct_unit`, `PointedSSet.reducedFreeTensorAct_assoc`: the action
  of `R~[-]` on `M~[-]` is unital and associative.
* `PointedSSet.reducedFreeTensorCompAct_unit`, `PointedSSet.reducedFreeTensorCompAct_assoc`: the
  unit and iteration laws of the action along a lax monoidal functor.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Chapter III.
* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace MathlibExt.SpectraSource.PointedSSet

noncomputable section

section Ring

variable (R : Type u) [Ring R]

/-- The reduced free `R`-module `R~[X]` on a pointed simplicial set `X`: its `n`-simplices form the
reduced free module on the `n`-simplices of `X` pointed at the basepoint, simplicial operators act
on generators, and the basepoint is zero. -/
-- The `n`-simplices of `R~[X]` unfold at implicit transparency to the module
-- `ReducedFreeModule R (X.point n)`, so that the module API applies to them.
@[expose, implicit_reducible]
def reducedFree : PointedSSet.{u} ⥤ PointedSSet.{u} where
  obj X :=
    { left := ⟨⟨⟩⟩
      right :=
        { obj n := ReducedFreeModule R (X.point n)
          map f := ↾(ReducedFreeModule.map R (X.right.map f ·) (X.map_point f))
          map_id n := by
            ext v
            induction v using ReducedFreeModule.induction_on <;> simp_all
          map_comp f g := by
            ext v
            induction v using ReducedFreeModule.induction_on <;> simp_all }
      hom :=
        { app n := ↾fun _ ↦ (0 : ReducedFreeModule R (X.point n))
          naturality _ _ _ := by ext; simp } }
  map {X Y} f := Under.homMk
    { app n := ↾(ReducedFreeModule.map R (f.right.app n ·) (app_point f n))
      naturality n m g := by
        ext v
        induction v using ReducedFreeModule.induction_on with
        | zero => simp
        | add v w _ _ => simp_all
        | smul_mk r x => simp }
    (by ext; simp)
  map_id X := by
    ext n v
    induction v using ReducedFreeModule.induction_on <;> simp_all
  map_comp f g := by
    ext n v
    induction v using ReducedFreeModule.induction_on <;> simp_all

variable {R} {X Y : PointedSSet.{u}} {n m : SimplexCategoryᵒᵖ}

@[simp]
lemma reducedFree_obj_point (X : PointedSSet.{u}) (n : SimplexCategoryᵒᵖ) :
    ((reducedFree R).obj X).point n = (0 : ReducedFreeModule R (X.point n)) :=
  -- The structure map of `R~[X]` is the constant map to `0` by definition, so the right-hand side
  -- of `hom_app` is `0` up to unfolding `reducedFree`.
  (hom_app ((reducedFree R).obj X) n (SSet.stdSimplex.const 0 0 n)).symm

/-- Simplicial operators act on `R~[X]` through their action on generators. -/
@[simp]
lemma reducedFree_obj_map (f : n ⟶ m) (v : ((reducedFree R).obj X).right.obj n) :
    ((reducedFree R).obj X).right.map f v =
      ReducedFreeModule.map R (X.right.map f ·) (X.map_point f) v := (rfl)

/-- A based map `f` acts on `R~[X]` through its action on generators. -/
@[simp]
lemma reducedFree_map_app (f : X ⟶ Y) (v : ((reducedFree R).obj X).right.obj n) :
    ((reducedFree R).map f).right.app n v =
      ReducedFreeModule.map R (f.right.app n ·) (app_point f n) v := (rfl)

variable (R) in
/-- The based map `X ⟶ R~[X]` sending each simplex to its generator; the basepoint goes to
zero. -/
def reducedFreeι (X : PointedSSet.{u}) : X ⟶ (reducedFree R).obj X :=
  Under.homMk
    { app n := ↾fun x : X.right.obj n ↦
        (ReducedFreeModule.mk R x : ((reducedFree R).obj X).right.obj n)
      naturality n m f := by
        ext x
        exact (ReducedFreeModule.map_mk R _ _ x).symm }
    (by
      ext n x
      exact (congrArg (ReducedFreeModule.mk R) (X.hom_app n x)).trans
        (ReducedFreeModule.mk_self R))

@[simp]
lemma reducedFreeι_right_app (x : X.right.obj n) :
    (reducedFreeι R X).right.app n x = ReducedFreeModule.mk R x := (rfl)

variable (R) in
/-- The natural based map `X ⟶ R~[X]` sending each simplex to its generator. -/
def toReducedFree : 𝟭 PointedSSet.{u} ⟶ reducedFree R where
  app X := reducedFreeι R X
  naturality X Y f := by
    ext n x
    exact (ReducedFreeModule.map_mk R _ _ x).symm

@[simp]
lemma toReducedFree_app (X : PointedSSet.{u}) : (toReducedFree R).app X = reducedFreeι R X :=
  (rfl)

end Ring

section CommRing

variable (R : Type u) [CommRing R]

/-- The external product of reduced free modules along the smash product commutes with
simplicial operators. -/
private lemma map₂_smashMk_map {X Y : PointedSSet.{u}} {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (v : ReducedFreeModule R (X.point n)) (w : ReducedFreeModule R (Y.point n)) :
    ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := m))
        (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _)
        (ReducedFreeModule.map R (X.right.map f ·) (X.map_point f) v)
        (ReducedFreeModule.map R (Y.right.map f ·) (Y.map_point f) w) =
      ReducedFreeModule.map R ((X ⊗ Y).right.map f ·) ((X ⊗ Y).map_point f)
        (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := n))
          (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _) v w) := by
  simp [ReducedFreeModule.map_map₂, ReducedFreeModule.map₂_map_left,
    ReducedFreeModule.map₂_map_right]

/-- The external product `R~[X] ∧ R~[Y] ⟶ R~[X ∧ Y]`, the bilinear extension of
`[x] ∧ [y] ↦ [x ∧ y]` on generators. -/
def reducedFreeμ (X Y : PointedSSet.{u}) :
    (reducedFree R).obj X ⊗ (reducedFree R).obj Y ⟶ (reducedFree R).obj (X ⊗ Y) :=
  smashLift
    { app n := ↾fun v : ((reducedFree R).obj X).right.obj n ×
          ((reducedFree R).obj Y).right.obj n ↦
        (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := n))
          (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _) v.1 v.2 :
          ((reducedFree R).obj (X ⊗ Y)).right.obj n)
      naturality n m f := by
        ext ⟨v, w⟩
        exact map₂_smashMk_map R f v w }
    (fun _ _ ↦ by
      rw [reducedFree_obj_point, reducedFree_obj_point]
      exact LinearMap.map_zero₂ (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y)) _ _) _)
    (fun _ _ ↦ by
      rw [reducedFree_obj_point, reducedFree_obj_point]
      exact LinearMap.map_zero (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y)) _ _ _))

variable {R} {X Y Z X' Y' : PointedSSet.{u}} {n : SimplexCategoryᵒᵖ}

/-- The external product sends a pair of elements to the bilinear extension of
`[x] ∧ [y] ↦ [x ∧ y]`. -/
@[simp]
lemma reducedFreeμ_app_smashMk (v : ((reducedFree R).obj X).right.obj n)
    (w : ((reducedFree R).obj Y).right.obj n) :
    (reducedFreeμ R X Y).right.app n (smashMk v w) =
      ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := n))
        (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _) v w :=
  smashLift_app_smashMk _ _ _ v w

/-- The reduced free module functor is lax monoidal for the smash product: the unit is the
generator map `S⁰ ⟶ R~[S⁰]` and the tensorator is the external product. -/
instance : (reducedFree R).LaxMonoidal where
  ε := reducedFreeι R (𝟙_ PointedSSet)
  μ := reducedFreeμ R
  μ_natural_left f X' := by
    ext n v w
    simp [ReducedFreeModule.map_map₂, ReducedFreeModule.map₂_map_left]
  μ_natural_right X' f := by
    ext n v w
    simp [ReducedFreeModule.map_map₂, ReducedFreeModule.map₂_map_right]
  associativity X Y Z := by
    ext n u w
    induction u using smashMk_induction with | h u v
    simp only [comp_right_app_apply, whiskerRight_app_smashMk, associator_hom_app_smashMk,
      whiskerLeft_app_smashMk, reducedFreeμ_app_smashMk, reducedFree_map_app,
      ReducedFreeModule.map_map₂]
    exact ReducedFreeModule.map₂_assoc _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun _ _ _ ↦ associator_hom_app_smashMk _ _ _) _ _ _
  left_unitality X := by
    ext n s v
    rcases eq_point_or_eq_tensorUnitSimplex s with rfl | rfl
    · simp
    · simp
  right_unitality X := by
    ext n v s
    rcases eq_point_or_eq_tensorUnitSimplex s with rfl | rfl
    · simp
    · simp

@[simp]
lemma reducedFree_ε : Functor.LaxMonoidal.ε (reducedFree R) = reducedFreeι R (𝟙_ PointedSSet) :=
  (rfl)

@[simp]
lemma reducedFree_μ (X Y : PointedSSet.{u}) :
    Functor.LaxMonoidal.μ (reducedFree R) X Y = reducedFreeμ R X Y := (rfl)

/-- The external product is compatible with the swap of smash factors, so the reduced free module
functor is lax braided. -/
instance : (reducedFree R).LaxBraided where
  braided X Y := by
    ext n v w
    simp only [reducedFree_μ, comp_right_app_apply, braiding_hom_app_smashMk,
      reducedFreeμ_app_smashMk, reducedFree_map_app, ReducedFreeModule.map_map₂]
    exact (ReducedFreeModule.map₂_swap R _ _ _ w v).symm

/-- Sending simplices to their generators is a monoidal natural transformation `X ⟶ R~[X]`. -/
instance : NatTrans.IsMonoidal (toReducedFree R) where
  unit := by simp
  tensor X Y := by
    ext n x y
    simp

end CommRing

section Tensor

open TensorProduct

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- The reduced free module `M~[X] = R~[X] ⊗_R M` with coefficients in an `R`-module `M` on a
pointed simplicial set `X`: its `n`-simplices are the finite formal sums `Σ xᵢ ⊗ mᵢ` of
`n`-simplices of `X` with coefficients in `M`, modulo the basepoint. Simplicial operators act on
generators, and the basepoint is zero. -/
-- The `n`-simplices of `M~[X]` unfold at implicit transparency to the module
-- `ReducedFreeModule R (X.point n) ⊗[R] M`, so that the module API applies to them.
@[expose, implicit_reducible]
def reducedFreeTensor : PointedSSet.{u} ⥤ PointedSSet.{u} where
  obj X :=
    { left := ⟨⟨⟩⟩
      right :=
        { obj n := ReducedFreeModule R (X.point n) ⊗[R] M
          map f :=
            ↾(LinearMap.rTensor M (ReducedFreeModule.map R (X.right.map f ·) (X.map_point f)))
          map_id n := by
            ext t
            induction t using TensorProduct.inductionOn <;> simp_all
          map_comp f g := by
            ext t
            induction t using TensorProduct.inductionOn <;> simp_all }
      hom :=
        { app n := ↾fun _ ↦ (0 : ReducedFreeModule R (X.point n) ⊗[R] M)
          naturality _ _ _ := by ext; simp } }
  map {X Y} f := Under.homMk
    { app n := ↾(LinearMap.rTensor M (ReducedFreeModule.map R (f.right.app n ·) (app_point f n)))
      naturality n m g := by
        ext t
        induction t using TensorProduct.inductionOn <;> simp_all }
    (by ext; simp)
  map_id X := by
    ext n t
    induction t using TensorProduct.inductionOn <;> simp_all
  map_comp f g := by
    ext n t
    induction t using TensorProduct.inductionOn <;> simp_all

variable {R M} {X Y Z : PointedSSet.{u}} {n m : SimplexCategoryᵒᵖ}

@[simp]
lemma reducedFreeTensor_obj_point (X : PointedSSet.{u}) (n : SimplexCategoryᵒᵖ) :
    ((reducedFreeTensor R M).obj X).point n =
      (0 : ReducedFreeModule R (X.point n) ⊗[R] M) :=
  -- The structure map of `M~[X]` is the constant map to `0` by definition, so the right-hand side
  -- of `hom_app` is `0` up to unfolding `reducedFreeTensor`.
  (hom_app ((reducedFreeTensor R M).obj X) n (SSet.stdSimplex.const 0 0 n)).symm

/-- Simplicial operators act on `M~[X]` through their action on generators. -/
@[simp]
lemma reducedFreeTensor_obj_map (f : n ⟶ m)
    (t : ((reducedFreeTensor R M).obj X).right.obj n) :
    ((reducedFreeTensor R M).obj X).right.map f t =
      LinearMap.rTensor M (ReducedFreeModule.map R (X.right.map f ·) (X.map_point f)) t := (rfl)

/-- A based map `f` acts on `M~[X]` through its action on generators. -/
@[simp]
lemma reducedFreeTensor_map_app (f : X ⟶ Y) (t : ((reducedFreeTensor R M).obj X).right.obj n) :
    ((reducedFreeTensor R M).map f).right.app n t =
      LinearMap.rTensor M (ReducedFreeModule.map R (f.right.app n ·) (app_point f n)) t := (rfl)

/-- The action of reduced free `R`-modules on reduced free modules with coefficients in `M` along
the smash product commutes with simplicial operators. -/
private lemma rTensor_map₂_smashMk_map {X Y : PointedSSet.{u}} {n m : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (v : ReducedFreeModule R (X.point n))
    (t : ReducedFreeModule R (Y.point n) ⊗[R] M) :
    LinearMap.rTensor M (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := m))
        (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _)
        (ReducedFreeModule.map R (X.right.map f ·) (X.map_point f) v))
        (LinearMap.rTensor M (ReducedFreeModule.map R (Y.right.map f ·) (Y.map_point f)) t) =
      LinearMap.rTensor M (ReducedFreeModule.map R ((X ⊗ Y).right.map f ·) ((X ⊗ Y).map_point f))
        (LinearMap.rTensor M (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := n))
          (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _) v) t) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp_all
  | tmul w x => simpa using congrArg (· ⊗ₜ[R] x) (map₂_smashMk_map R f v w)

variable (R M) in
/-- The action `R~[X] ∧ M~[Y] ⟶ M~[X ∧ Y]` of reduced free `R`-modules on reduced free modules with
coefficients in `M`: the bilinear extension of `[x] ∧ ([y] ⊗ m) ↦ [x ∧ y] ⊗ m`. -/
def reducedFreeTensorAct (X Y : PointedSSet.{u}) :
    (reducedFree R).obj X ⊗ (reducedFreeTensor R M).obj Y ⟶
      (reducedFreeTensor R M).obj (X ⊗ Y) :=
  smashLift
    { app n := ↾fun v : ((reducedFree R).obj X).right.obj n ×
          ((reducedFreeTensor R M).obj Y).right.obj n ↦
        (LinearMap.rTensor M (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := n))
          (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _) v.1) v.2 :
          ((reducedFreeTensor R M).obj (X ⊗ Y)).right.obj n)
      naturality n m f := by
        ext ⟨v, t⟩
        exact rTensor_map₂_smashMk_map f v t }
    (fun _ _ ↦ by
      rw [reducedFree_obj_point, reducedFreeTensor_obj_point]
      exact LinearMap.map_zero₂ (LinearMap.rTensorHom M ∘ₗ
        ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y))
          (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _)) _)
    (fun n v ↦ by
      rw [reducedFreeTensor_obj_point, reducedFreeTensor_obj_point]
      exact LinearMap.map_zero (LinearMap.rTensor M (ReducedFreeModule.map₂ R
        (smashMk (X := X) (Y := Y) (n := n)) (fun _ ↦ smashMk_point_left _)
        (fun _ ↦ smashMk_point_right _) v)))

/-- The action sends `v ∧ t` to the bilinear extension of `[x] ∧ ([y] ⊗ m) ↦ [x ∧ y] ⊗ m`. -/
@[simp]
lemma reducedFreeTensorAct_app_smashMk (v : ((reducedFree R).obj X).right.obj n)
    (t : ((reducedFreeTensor R M).obj Y).right.obj n) :
    (reducedFreeTensorAct R M X Y).right.app n (smashMk v t) =
      LinearMap.rTensor M (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := n))
        (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _) v) t :=
  smashLift_app_smashMk _ _ _ v t

/-- The action `R~[X] ∧ M~[Y] ⟶ M~[X ∧ Y]` is natural in `X`. -/
@[reassoc]
lemma reducedFreeTensorAct_naturality_left {X X' : PointedSSet.{u}} (f : X ⟶ X')
    (Y : PointedSSet.{u}) :
    (reducedFree R).map f ▷ _ ≫ reducedFreeTensorAct R M X' Y =
      reducedFreeTensorAct R M X Y ≫ (reducedFreeTensor R M).map (f ▷ Y) := by
  ext n v t
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp_all
  | tmul w m => simp [ReducedFreeModule.map_map₂, ReducedFreeModule.map₂_map_left]

/-- The action `R~[X] ∧ M~[Y] ⟶ M~[X ∧ Y]` is natural in `Y`. -/
@[reassoc]
lemma reducedFreeTensorAct_naturality_right (X : PointedSSet.{u}) {Y Y' : PointedSSet.{u}}
    (g : Y ⟶ Y') :
    _ ◁ (reducedFreeTensor R M).map g ≫ reducedFreeTensorAct R M X Y' =
      reducedFreeTensorAct R M X Y ≫ (reducedFreeTensor R M).map (X ◁ g) := by
  ext n v t
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp_all
  | tmul w m => simp [ReducedFreeModule.map_map₂, ReducedFreeModule.map₂_map_right]

/-- Unitality of the action: the generator of `S⁰` acts as the identity. -/
@[reassoc]
lemma reducedFreeTensorAct_unit (Y : PointedSSet.{u}) :
    reducedFreeι R (𝟙_ _) ▷ _ ≫ reducedFreeTensorAct R M (𝟙_ _) Y =
      (λ_ ((reducedFreeTensor R M).obj Y)).hom ≫ (reducedFreeTensor R M).map (λ_ Y).inv := by
  ext n s t
  rcases eq_point_or_eq_tensorUnitSimplex s with rfl | rfl
  · simp
  · induction t using TensorProduct.inductionOn <;> simp_all

/-- Associativity of the action, over the external product of reduced free `R`-modules. -/
@[reassoc]
lemma reducedFreeTensorAct_assoc (X Y Z : PointedSSet.{u}) :
    reducedFreeμ R X Y ▷ _ ≫ reducedFreeTensorAct R M (X ⊗ Y) Z =
      (α_ _ _ _).hom ≫ _ ◁ reducedFreeTensorAct R M Y Z ≫ reducedFreeTensorAct R M X (Y ⊗ Z) ≫
        (reducedFreeTensor R M).map (α_ X Y Z).inv := by
  ext n z t
  induction z using smashMk_induction with | h u v
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp_all
  | tmul w m =>
    simp only [comp_right_app_apply, whiskerRight_app_smashMk, reducedFreeμ_app_smashMk,
      reducedFreeTensorAct_app_smashMk, associator_hom_app_smashMk, whiskerLeft_app_smashMk,
      reducedFreeTensor_map_app, LinearMap.rTensor_tmul, ReducedFreeModule.map_map₂]
    congr 1
    exact ReducedFreeModule.map₂_assoc R smashMk _ _ smashMk _ _ smashMk _ _
      (fun x y ↦ (α_ X Y Z).inv.right.app n (smashMk x y)) _ _
      (fun x y w ↦ (associator_inv_app_smashMk x y w).symm) u v w

section Map

variable {N P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

variable (R) in
/-- The change of coefficients `M~[X] ⟶ N~[X]` along a linear map `g : M →ₗ[R] N`, applying `g` to
the coefficients: `Σ xᵢ ⊗ mᵢ ↦ Σ xᵢ ⊗ g mᵢ`. It is natural in `X`. -/
def reducedFreeTensorMap (g : M →ₗ[R] N) : reducedFreeTensor R M ⟶ reducedFreeTensor R N where
  app X := Under.homMk
    { app n := ↾(LinearMap.lTensor (ReducedFreeModule R (X.point n)) g)
      naturality n m f := by
        ext t
        induction t using TensorProduct.inductionOn <;> simp_all }
    (by ext; simp)
  naturality X Y f := by
    ext n t
    induction t using TensorProduct.inductionOn <;> simp_all

@[simp]
lemma reducedFreeTensorMap_app_right_app (g : M →ₗ[R] N)
    (t : ((reducedFreeTensor R M).obj X).right.obj n) :
    ((reducedFreeTensorMap R g).app X).right.app n t =
      LinearMap.lTensor (ReducedFreeModule R (X.point n)) g t := (rfl)

@[simp]
lemma reducedFreeTensorMap_id : reducedFreeTensorMap R (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  ext X n t
  simp

lemma reducedFreeTensorMap_comp (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    reducedFreeTensorMap R (h ∘ₗ g) = reducedFreeTensorMap R g ≫ reducedFreeTensorMap R h := by
  ext X n t
  simp [LinearMap.lTensor_comp_apply]

/-- The change of coefficients is compatible with the action of reduced free `R`-modules. -/
@[reassoc (attr := simp)]
lemma reducedFreeTensorAct_comp_reducedFreeTensorMap_app (g : M →ₗ[R] N)
    (X Y : PointedSSet.{u}) :
    reducedFreeTensorAct R M X Y ≫ (reducedFreeTensorMap R g).app (X ⊗ Y) =
      _ ◁ (reducedFreeTensorMap R g).app Y ≫ reducedFreeTensorAct R N X Y := by
  ext n v t
  induction t using TensorProduct.inductionOn <;> simp_all

end Map

section Comp

open scoped ExternalProduct

variable {C : Type*} [Category* C] [MonoidalCategory C] (K : C ⥤ PointedSSet.{u}) [K.LaxMonoidal]

variable (R M) in
/-- The action `R~[K p] ∧ M~[K q] ⟶ M~[K (p ⊗ q)]` along a lax monoidal functor `K` to pointed
simplicial sets: the action of reduced free `R`-modules followed by the tensorator of `K`. With
the unit and associativity laws `reducedFreeTensorCompAct_unit` and
`reducedFreeTensorCompAct_assoc`, these are the structure maps of a module over the lax monoidal
functor `K ⋙ reducedFree R`. -/
def reducedFreeTensorCompAct :
    (K ⋙ reducedFree R) ⊠ (K ⋙ reducedFreeTensor R M) ⟶ tensor C ⋙ K ⋙ reducedFreeTensor R M where
  app pq := reducedFreeTensorAct R M _ _ ≫ (reducedFreeTensor R M).map
    (Functor.LaxMonoidal.μ K pq.1 pq.2)
  naturality pq pq' f := by
    simp only [Functor.comp_obj, externalProductBifunctor_obj_obj,
      externalProductBifunctor_obj_map, Functor.comp_map, tensor_map, tensorHom_def,
      Category.assoc, reducedFreeTensorAct_naturality_right_assoc,
      reducedFreeTensorAct_naturality_left_assoc, ← Functor.map_comp]
    rw [← tensorHom_def_assoc, Functor.LaxMonoidal.μ_natural, tensorHom_def]

@[simp]
lemma reducedFreeTensorCompAct_app (p q : C) :
    (reducedFreeTensorCompAct R M K).app (p, q) =
      reducedFreeTensorAct R M (K.obj p) (K.obj q) ≫
        (reducedFreeTensor R M).map (Functor.LaxMonoidal.μ K p q) := (rfl)

/-- Unitality of the action along a lax monoidal functor `K`. -/
lemma reducedFreeTensorCompAct_unit (q : C) :
    Functor.LaxMonoidal.ε (K ⋙ reducedFree R) ▷ (K ⋙ reducedFreeTensor R M).obj q ≫
        (reducedFreeTensorCompAct R M K).app (𝟙_ C, q) =
      (λ_ _).hom ≫ (K ⋙ reducedFreeTensor R M).map (λ_ q).inv := by
  simp only [Functor.LaxMonoidal.comp_ε, reducedFree_ε, comp_whiskerRight, Category.assoc,
    Functor.comp_obj, Functor.comp_map, reducedFreeTensorCompAct_app,
    reducedFreeTensorAct_naturality_left_assoc, reducedFreeTensorAct_unit_assoc,
    ← Functor.map_comp]
  rw [Functor.LaxMonoidal.left_unitality_inv]

/-- Associativity of the action along a lax monoidal functor `K`. -/
lemma reducedFreeTensorCompAct_assoc (p q r : C) :
    Functor.LaxMonoidal.μ (K ⋙ reducedFree R) p q ▷ (K ⋙ reducedFreeTensor R M).obj r ≫
        (reducedFreeTensorCompAct R M K).app (p ⊗ q, r) =
      (α_ _ _ _).hom ≫ (K ⋙ reducedFree R).obj p ◁ (reducedFreeTensorCompAct R M K).app (q, r) ≫
        (reducedFreeTensorCompAct R M K).app (p, q ⊗ r) ≫
          (K ⋙ reducedFreeTensor R M).map (α_ p q r).inv := by
  simp only [Functor.LaxMonoidal.comp_μ, reducedFree_μ, comp_whiskerRight, Category.assoc,
    Functor.comp_obj, Functor.comp_map, reducedFreeTensorCompAct_app,
    reducedFreeTensorAct_naturality_left_assoc, reducedFreeTensorAct_assoc_assoc,
    whiskerLeft_comp, reducedFreeTensorAct_naturality_right_assoc, ← Functor.map_comp]
  rw [Functor.LaxMonoidal.associativity_inv]

/-- The action along a lax monoidal functor `K` sends `v ∧ Σ yᵢ ⊗ mᵢ` to `Σ μ(v ∧ yᵢ) ⊗ mᵢ`, the
bilinear extension of `[x] ∧ ([y] ⊗ m) ↦ [μ (x ∧ y)] ⊗ m` for the tensorator `μ` of `K`. -/
lemma reducedFreeTensorCompAct_app_app_smashMk (p q : C)
    (v : ((reducedFree R).obj (K.obj p)).right.obj n)
    (t : ((reducedFreeTensor R M).obj (K.obj q)).right.obj n) :
    ((reducedFreeTensorCompAct R M K).app (p, q)).right.app n (smashMk v t) =
      LinearMap.rTensor M (ReducedFreeModule.map₂ R
        (fun x y ↦ (Functor.LaxMonoidal.μ K p q).right.app n (smashMk x y)) (by simp) (by simp) v)
        t := by
  rw [reducedFreeTensorCompAct_app, comp_right_app_apply, reducedFreeTensorAct_app_smashMk,
    reducedFreeTensor_map_app, ← LinearMap.rTensor_comp_apply]
  congr 2
  exact LinearMap.ext fun w ↦ ReducedFreeModule.map_map₂ R _ _ _ _ _ v w

/-- Composing the action along `K` with the generators `K p ⟶ R~[K p]` sends `x ∧ Σ yᵢ ⊗ mᵢ` to
`Σ μ(x ∧ yᵢ) ⊗ mᵢ`. -/
lemma reducedFreeι_whiskerRight_comp_reducedFreeTensorCompAct_app_app_smashMk (p q : C)
    (x : (K.obj p).right.obj n) (t : ((reducedFreeTensor R M).obj (K.obj q)).right.obj n) :
    (reducedFreeι R (K.obj p) ▷ (reducedFreeTensor R M).obj (K.obj q) ≫
      (reducedFreeTensorCompAct R M K).app (p, q)).right.app n
        (smashMk x t) =
      LinearMap.rTensor M (ReducedFreeModule.map R
        (fun y ↦ (Functor.LaxMonoidal.μ K p q).right.app n (smashMk x y)) (by simp)) t := by
  rw [comp_right_app_apply, whiskerRight_app_smashMk, reducedFreeι_right_app,
    reducedFreeTensorCompAct_app_app_smashMk]
  congr 2
  exact LinearMap.ext (ReducedFreeModule.map₂_mk_left R _ _ _ x)

/-- The change of coefficients is compatible with the action along a lax monoidal functor `K`. -/
@[reassoc]
lemma reducedFreeTensorCompAct_app_comp_reducedFreeTensorMap_app {N : Type u} [AddCommGroup N]
    [Module R N] (g : M →ₗ[R] N) (p q : C) :
    (reducedFreeTensorCompAct R M K).app (p, q) ≫ (reducedFreeTensorMap R g).app (K.obj (p ⊗ q)) =
      (K ⋙ reducedFree R).obj p ◁ (reducedFreeTensorMap R g).app (K.obj q) ≫
        (reducedFreeTensorCompAct R N K).app (p, q) := by
  simp

end Comp

end Tensor

end

end MathlibExt.SpectraSource.PointedSSet
