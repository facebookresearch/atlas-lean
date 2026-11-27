/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.BarFunctorial

/-!
# Algebra-valued two-sided monadic bar construction

For a monad `T` on `C`, a right `T`-module `R : C ⥤ D`, and a `T`-algebra `alg`,
the algebra-valued bar `B(R,T,alg) : SimplicialObject D` is the Cat-valued
two-sided bar at the terminal-index left module of `alg`, evaluated at the
unique discrete point with Mathlib's `evaluation` functor.

In degree `n` this is `R(Tⁿ(alg.A))`; faces and degeneracies are inherited from
the two-sided bar, hence functorial in right-module and algebra morphisms via
`twoSidedBarHom` and its identity/composition laws.

No new simplicial identity is proved: every computation below unfolds to a
`twoSidedBar_*` lemma. No augmentation, contraction, Eilenberg--Moore
comparison, or derived statement is claimed here. The bundled bifunctor
`algebraBarFunctor` below is the composite of `algebraLeftModuleFunctor`,
the general `twoSidedBarFunctor`, and point evaluation; its object and map lemmas
are `rfl`, so no simplicial or functor law is reproved.

Mathematical source: J. P. May, *The Geometry of Iterated Loop Spaces*,
Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.
This file is the object-valued specialization of May's functor-valued
two-sided bar `B(R,T,L)`: the left module is the terminal-index module of
the algebra, evaluated at the discrete point. Degree and face/degeneracy
conventions are inherited from `Bar`.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {T : Monad C}

section AlgebraLeftModule

/--
Terminal-index left `T`-module of a `T`-algebra: the constant functor at
`alg.A` with action `alg.a`.
-/
def algebraLeftModule (alg : T.Algebra) : LeftModule (Discrete PUnit.{1}) T :=
  LeftModule.mk ((Functor.const (Discrete PUnit.{1})).obj alg.A)
    { app := fun _ => alg.a
      naturality := fun _ _ _ => by
        change T.map (𝟙 alg.A) ≫ alg.a = alg.a ≫ 𝟙 alg.A
        simp only [Functor.map_id, Category.id_comp, Category.comp_id] }
    (fun _ => alg.unit)
    (fun _ => alg.assoc)

/-- The underlying functor is the constant functor at `alg.A`. -/
@[simp]
theorem algebraLeftModule_functor (alg : T.Algebra) :
    (algebraLeftModule alg).functor = (Functor.const (Discrete PUnit.{1})).obj alg.A :=
  rfl

/-- The action is pointwise the algebra structure map. -/
@[simp]
theorem algebraLeftModule_action_app (alg : T.Algebra) (X : Discrete PUnit.{1}) :
    (algebraLeftModule alg).action.app X = alg.a :=
  rfl

/-- Morphism of terminal-index left modules induced by an algebra morphism. -/
def algebraLeftModuleHom {alg₁ alg₂ : T.Algebra} (φ : alg₁ ⟶ alg₂) :
    algebraLeftModule alg₁ ⟶ algebraLeftModule alg₂ where
  f :=
    { app := fun _ => φ.f
      naturality := fun _ _ _ => by
        change 𝟙 alg₁.A ≫ φ.f = φ.f ≫ 𝟙 alg₂.A
        simp only [Category.id_comp, Category.comp_id] }
  h := by
    ext X
    exact φ.h

/-- The underlying map is pointwise the algebra morphism. -/
@[simp]
theorem algebraLeftModuleHom_f_app {alg₁ alg₂ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (X : Discrete PUnit.{1}) :
    (algebraLeftModuleHom φ).f.app X = φ.f :=
  rfl

/-- Identity algebra morphisms induce identity module morphisms. -/
theorem algebraLeftModuleHom_id (alg : T.Algebra) :
    algebraLeftModuleHom (𝟙 alg) = 𝟙 (algebraLeftModule alg) :=
  Algebra.Hom.ext' _ _ _ _ (by ext X; simp [algebraLeftModuleHom, algebraLeftModule])

/-- Composition of algebra morphisms induces composition of module morphisms. -/
theorem algebraLeftModuleHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    algebraLeftModuleHom φ ≫ algebraLeftModuleHom ψ =
      algebraLeftModuleHom (φ ≫ ψ) :=
  Algebra.Hom.ext' _ _ _ _ (by ext X; simp [algebraLeftModuleHom])

/-- Functorial lift from `T`-algebras to terminal-index left modules. -/
def algebraLeftModuleFunctor : T.Algebra ⥤ LeftModule (Discrete PUnit.{1}) T where
  obj alg := algebraLeftModule alg
  map φ := algebraLeftModuleHom φ
  map_id alg := algebraLeftModuleHom_id alg
  map_comp φ ψ := (algebraLeftModuleHom_comp φ ψ).symm

end AlgebraLeftModule

section AlgebraBar

/--
Algebra-valued two-sided bar: `twoSidedBar` at the algebra left module,
evaluated at the unique discrete point.
-/
noncomputable def algebraBar (R : RightModule T D) (alg : T.Algebra) :
    SimplicialObject D :=
  twoSidedBar T R (algebraLeftModule alg) ⋙
    (evaluation (Discrete PUnit.{1}) D).obj ⟨PUnit.unit⟩

/--
Degree `n` is `R(Tⁿ(alg.A))`, by `rfl` through evaluation at the discrete point;
cf. `twoSidedBar_obj_obj`.
-/
@[simp]
theorem algebraBar_obj (R : RightModule T D) (alg : T.Algebra) (n : ℕ) :
    (algebraBar R alg).obj (Opposite.op (SimplexCategory.mk n)) =
      R.functor.obj ((monadPow T n).obj alg.A) :=
  rfl

/-- Degree zero is `R(alg.A)`. -/
@[simp]
theorem algebraBar_obj_zero (R : RightModule T D) (alg : T.Algebra) :
    (algebraBar R alg).obj (Opposite.op (SimplexCategory.mk 0)) =
      R.functor.obj alg.A :=
  rfl

/-- Faces are the two-sided faces evaluated at the discrete point. -/
@[simp]
theorem algebraBar_map_δ_op (R : RightModule T D) (alg : T.Algebra) {n : ℕ}
    (i : Fin (n + 2)) :
    (algebraBar R alg).map (SimplexCategory.δ i).op =
      barFaceApp (T := T) (R := R) (L := algebraLeftModule alg) n i ⟨PUnit.unit⟩ := by
  change ((evaluation (Discrete PUnit.{1}) D).obj ⟨PUnit.unit⟩).map
    ((twoSidedBar T R (algebraLeftModule alg)).map (SimplexCategory.δ i).op) = _
  rw [twoSidedBar_map_δ_op]
  rfl

/-- Degeneracies insert the unit via `barEtaAtPos` at `alg.A`. -/
@[simp]
theorem algebraBar_map_σ_op (R : RightModule T D) (alg : T.Algebra) {n : ℕ}
    (i : Fin (n + 1)) :
    (algebraBar R alg).map (SimplexCategory.σ i).op =
      R.functor.map (barEtaAtPos T n i alg.A) := by
  change ((evaluation (Discrete PUnit.{1}) D).obj ⟨PUnit.unit⟩).map
    ((twoSidedBar T R (algebraLeftModule alg)).map (SimplexCategory.σ i).op) = _
  rw [twoSidedBar_map_σ_op]
  rfl

/-- Morphism of algebra-valued bars from a right-module and algebra morphism. -/
noncomputable def algebraBarHom {R R' : RightModule T D} {alg alg' : T.Algebra}
    (fR : R ⟶ R') (φ : alg ⟶ alg') : algebraBar R alg ⟶ algebraBar R' alg' :=
  Functor.whiskerRight (twoSidedBarHom fR (algebraLeftModuleHom φ))
    ((evaluation (Discrete PUnit.{1}) D).obj ⟨PUnit.unit⟩)

/-- Identity morphisms induce the identity bar morphism. -/
theorem algebraBarHom_id (R : RightModule T D) (alg : T.Algebra) :
    algebraBarHom (𝟙 R) (𝟙 alg) = 𝟙 (algebraBar R alg) := by
  unfold algebraBarHom algebraBar
  rw [algebraLeftModuleHom_id, twoSidedBarHom_id, Functor.whiskerRight_id']

/-- Composition of morphisms induces composition of bar morphisms. -/
theorem algebraBarHom_comp {R R' R'' : RightModule T D} {alg alg' alg'' : T.Algebra}
    (fR : R ⟶ R') (gR : R' ⟶ R'') (φ : alg ⟶ alg') (ψ : alg' ⟶ alg'') :
    algebraBarHom fR φ ≫ algebraBarHom gR ψ =
      algebraBarHom (fR ≫ gR) (φ ≫ ψ) := by
  unfold algebraBarHom algebraBar
  rw [← Functor.whiskerRight_comp, twoSidedBarHom_comp, algebraLeftModuleHom_comp]

/--
Bundled algebra-valued bar bifunctor, as composite of
`algebraLeftModuleFunctor`, the general `twoSidedBarFunctor`, and point evaluation.
-/
noncomputable def algebraBarFunctor :
    (RightModule T D) × T.Algebra ⥤ SimplicialObject D :=
  (Functor.id (RightModule T D)).prod algebraLeftModuleFunctor ⋙
    twoSidedBarFunctor T ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ (Discrete PUnit.{1} ⥤ D) D).obj
      ((evaluation (Discrete PUnit.{1}) D).obj ⟨PUnit.unit⟩)

/-- Object computation: bundling recovers `algebraBar`, by `rfl`. -/
@[simp]
theorem algebraBarFunctor_obj (R : RightModule T D) (alg : T.Algebra) :
    algebraBarFunctor.obj (R, alg) = algebraBar R alg :=
  rfl

/-- Map computation: bundling recovers `algebraBarHom`, by `rfl`. -/
@[simp]
theorem algebraBarFunctor_map {p q : (RightModule T D) × T.Algebra} (f : p ⟶ q) :
    algebraBarFunctor.map f = algebraBarHom f.1 f.2 :=
  rfl

end AlgebraBar

end Monad
end CategoryTheory
