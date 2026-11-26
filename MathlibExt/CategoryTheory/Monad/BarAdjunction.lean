/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Monad.BarChange
public import MathlibExt.CategoryTheory.Monad.BarEilenbergMoore
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# The two-sided bar of an adjunction

Let F : C → D and U : D → C form an adjunction F ⊣ U, with unit η, counit ε, and induced monad
T=UF. The left adjoint is a right T-module with action ε_{F(X)}, and the right adjoint is a
left T-module with action U(ε_Y).

Their two-sided bar is a simplicial endofunctor of D with B_n(Y)=F(T^n(UY)). Its first and
last faces use the right and left module actions; the inner faces use monad multiplication,
and degeneracies insert the unit, indexed from the right-module end. The counit gives an
augmentation to the identity endofunctor of D. Free-forgetful adjunction comparisons also give
augmented morphisms to the underlying Eilenberg–Moore bar.

The two-sided bar convention follows J. P. May, *The Geometry of Iterated Loop Spaces*,
Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9, Construction 9.6 and Remark 9.12,
<https://doi.org/10.1007/BFb0067491>. The category object and morphism universes are
independent.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} {U : D ⥤ C}

section AdjModules

/-- Let F : C ⥤ D and U : D ⥤ C form an adjunction with counit ε and monad T=UF on C. The functor
F is a right T-module, with action F(TX)=F(U(FX)) → F(X) given by ε_{F(X)}. The unit law is
the left triangle identity and associativity is counit naturality. The categories C,D may have
independent object and morphism universes. -/
def adjRightModule (adj : F ⊣ U) : RightModule adj.toMonad D :=
  RightModule.mk F
    { app := fun X => adj.counit.app (F.obj X)
      naturality := fun _X _Y f => adj.counit.naturality (F.map f) }
    (fun X => adj.left_triangle_components X)
    (fun X => adj.counit.naturality (adj.counit.app (F.obj X)))

/-- For an adjunction F : C ⥤ D, U : D ⥤ C with F ⊣ U, the underlying functor of the canonical
right module over T=UF is F. Its action is the counit at F(X), so the module retains the left
adjoint as its carrier functor. -/
@[simp]
theorem adjRightModule_functor (adj : F ⊣ U) :
    (adjRightModule adj).functor = F :=
  rfl

/-- Let F ⊣ U be an adjunction, T=UF its monad, and X ∈ C. The action component of the canonical
right T-module F is ε_{F(X)} : F(U(FX)) → F(X). This is the counit at the object F(X). -/
@[simp]
theorem adjRightModule_action_app (adj : F ⊣ U) (X : C) :
    (adjRightModule adj).action.app X = adj.counit.app (F.obj X) :=
  rfl

/-- Let F : C ⥤ D and U : D ⥤ C form an adjunction with monad T=UF. The functor U is a left
T-module, with action T(UY)=U(F(UY)) → UY given by U(ε_Y). The unit law is the right triangle
identity, and the left-module associativity equation follows from naturality of the counit. No
monadicity assumption is needed. -/
def adjLeftModule (adj : F ⊣ U) : LeftModule D adj.toMonad :=
  LeftModule.mk U
    { app := fun Y => U.map (adj.counit.app Y)
      naturality := fun Y₁ Y₂ g => by
        have h := congrArg (U.map) (adj.counit.naturality g)
        simp only [Functor.map_comp, Functor.id_map] at h
        exact h }
    (fun Y => adj.right_triangle_components Y)
    (fun Y => by
      have h :=
        congrArg (U.map) (adj.counit.naturality (adj.counit.app Y))
      simp only [Functor.map_comp, Functor.id_map] at h
      exact h.symm)

/-- For an adjunction F : C ⥤ D, U : D ⥤ C with F ⊣ U, the canonical left module over the monad
T=UF has underlying functor U. Its action on an object Y ∈ D is U applied to the adjunction
counit ε_Y. -/
@[simp]
theorem adjLeftModule_functor (adj : F ⊣ U) :
    (adjLeftModule adj).functor = U :=
  rfl

/-- Let F ⊣ U be an adjunction, T=UF its monad, and Y ∈ D. The action component of the canonical
left T-module U equals U(ε_Y) : T(UY) → UY. The counit is that of the given adjunction. -/
@[simp]
theorem adjLeftModule_action_app (adj : F ⊣ U) (Y : D) :
    (adjLeftModule adj).action.app Y = U.map (adj.counit.app Y) :=
  rfl

end AdjModules

section AdjBar

/-- Let F : C ⥤ D and U : D ⥤ C form an adjunction and put T=UF. The two-sided bar of the right
T-module F and left T-module U is a simplicial object in D ⥤ D. Its degree-n endofunctor sends
Y to F(T^n(UY)), its endpoint faces use ε_F and Uε, its middle faces use multiplication of T,
and its degeneracies insert the monad unit. -/
noncomputable def adjBar (adj : F ⊣ U) : SimplicialObject (D ⥤ D) :=
  twoSidedBar adj.toMonad (adjRightModule adj) (adjLeftModule adj)

/-- For an adjunction F ⊣ U and n ∈ ℕ, the value of its simplicial bar at the opposite simplex [n]
is the two-sided bar functor B(F,UF,U)_n. Its value at Y ∈ D is F((UF)^n(UY)). This identifies
the simplicial degree with the corresponding levelwise bar endofunctor. -/
@[simp]
theorem adjBar_obj (adj : F ⊣ U) (n : ℕ) :
    (adjBar adj).obj (Opposite.op (SimplexCategory.mk n)) =
      barObj adj.toMonad (adjRightModule adj) (adjLeftModule adj) n :=
  rfl

/-- Let F ⊣ U be an adjunction, T=UF, n ∈ ℕ, and Y ∈ D. The degree-n object of the evaluated
adjunction bar is exactly F(T^n(UY)), with T^n=monadPow(T,n). Thus degree zero is F(UY), and
each higher degree inserts another induced-monad factor. -/
@[simp]
theorem adjBar_obj_obj (adj : F ⊣ U) (n : ℕ) (Y : D) :
    ((adjBar adj).obj (Opposite.op (SimplexCategory.mk n))).obj Y =
      F.obj ((monadPow adj.toMonad n).obj (U.obj Y)) :=
  rfl

/-- For an adjunction F ⊣ U, T=UF, n ∈ ℕ, and g : Y → Z in D, the degree-n bar endofunctor acts by
F(T^n(U(g))) : F(T^n(UY)) → F(T^n(UZ)). This is the map on the object variable of D, distinct
from the simplicial faces and degeneracies. -/
@[simp]
theorem adjBar_obj_map (adj : F ⊣ U) {n : ℕ} {Y Z : D} (g : Y ⟶ Z) :
    ((adjBar adj).obj (Opposite.op (SimplexCategory.mk n))).map g =
      F.map ((monadPow adj.toMonad n).map (U.map g)) :=
  rfl

/-- Let F : C ⥤ D and U : D ⥤ C form an adjunction. Its bar in simplicial degree zero is U ⋙ F,
the endofunctor Y ↦ F(UY) on D. This is the underlying functor of the comonad induced by the
adjunction. -/
theorem adjBar_obj_zero (adj : F ⊣ U) :
    (adjBar adj).obj (Opposite.op (SimplexCategory.mk 0)) = U ⋙ F :=
  barObj_zero adj.toMonad (adjRightModule adj) (adjLeftModule adj)

/-- Let F ⊣ U be an adjunction, T=UF, n ∈ ℕ, and i ∈ Fin(n+2). The simplicial face d_i : B_{n+1} →
B_n equals barFace(T,adjRightModule,adjLeftModule,n,i). The first face is the right action
ε_F, the last is F(T^n(Uε)), and interior faces apply F to monad multiplication at reversed
index Fin.rev(i−1). -/
@[simp]
theorem adjBar_map_δ_op (adj : F ⊣ U) {n : ℕ} (i : Fin (n + 2)) :
    (adjBar adj).map (SimplexCategory.δ i).op =
      barFace (T := adj.toMonad) (R := adjRightModule adj)
        (L := adjLeftModule adj) n i :=
  twoSidedBar_map_δ_op _ _ _ _

/-- For an adjunction F ⊣ U, T=UF, n ∈ ℕ, and i ∈ Fin(n+1), the simplicial degeneracy B_n →
B_{n+1} equals the two-sided bar degeneracy of the canonical modules F and U. At Y it is F
applied to the unit insertion barEtaAtPos(T,n,i,UY), whose raw position is Fin.rev(i). -/
@[simp]
theorem adjBar_map_σ_op (adj : F ⊣ U) {n : ℕ} (i : Fin (n + 1)) :
    (adjBar adj).map (SimplexCategory.σ i).op =
      barDegeneracy (T := adj.toMonad) (R := adjRightModule adj)
        (L := adjLeftModule adj) n i :=
  twoSidedBar_map_σ_op _ _ _ _

/-- Let F ⊣ U be an adjunction, T=UF, n ∈ ℕ, i ∈ Fin(n+2), and Y ∈ D. The face component
F(T^{n+1}(UY)) → F(T^n(UY)) is the elementary two-sided bar face. At i=0 it is the iterated
right action, equivalently the counit at F(T^n(UY)) with the canonical power identification.
At i=n+1 it is F(T^n(U(ε_Y))); otherwise it is F applied to the multiplication insertion with
raw reversed index Fin.rev(i−1). -/
@[simp]
theorem adjBar_map_δ_op_app (adj : F ⊣ U) {n : ℕ} (i : Fin (n + 2))
    (Y : D) :
    ((adjBar adj).map (SimplexCategory.δ i).op).app Y =
      barFaceApp (T := adj.toMonad) (R := adjRightModule adj)
        (L := adjLeftModule adj) n i Y := by
  rw [adjBar_map_δ_op]
  rfl

/-- Let F ⊣ U be an adjunction, T=UF, n ∈ ℕ, i ∈ Fin(n+1), and Y ∈ D. The degree-n degeneracy
component is F(barEtaAtPos(T,n,i,UY)) : F(T^n(UY)) → F(T^{n+1}(UY)). The insertion is etaAtPos
with the reversed finite position Fin.rev(i), so the simplicial index counts from the
right-module end. -/
@[simp]
theorem adjBar_map_σ_op_app (adj : F ⊣ U) {n : ℕ} (i : Fin (n + 1))
    (Y : D) :
    ((adjBar adj).map (SimplexCategory.σ i).op).app Y =
      F.map (barEtaAtPos adj.toMonad n i (U.obj Y)) := by
  rw [adjBar_map_σ_op]
  rfl

end AdjBar

section AdjAugmentation

/-- For an adjunction F ⊣ U, the natural transformation ε : F∘U → Id_D is the degree-zero pairing
of B(F,UF,U). Its domain is the zero-degree bar endofunctor Y ↦ F(UY) and its target is the
identity endofunctor of D. -/
def adjPairing (adj : F ⊣ U) :
    barObj adj.toMonad (adjRightModule adj) (adjLeftModule adj) 0 ⟶ 𝟭 D :=
  adj.counit

/-- Let F ⊣ U be an adjunction and Y ∈ D. The component at Y of the degree-zero bar pairing is ε_Y
: F(UY) → Y. Thus the pairing used for the bar augmentation is the specified adjunction
counit. -/
@[simp]
theorem adjPairing_app (adj : F ⊣ U) (Y : D) :
    (adjPairing adj).app Y = adj.counit.app Y :=
  rfl

/-- For an adjunction F ⊣ U with T=UF, the counit pairing B(F,T,U)_0 → Id_D is balanced. At Y ∈ D
its two degree-one face composites satisfy ε_{F(UY)} ≫ ε_Y = F(U(ε_Y)) ≫ ε_Y by counit
naturality. Hence the canonical right action on F and left action on U give a balanced pairing
to the identity endofunctor. -/
noncomputable def adjBalancedPairing (adj : F ⊣ U) :
    BalancedPairing adj.toMonad (adjRightModule adj) (adjLeftModule adj) :=
  BalancedPairing.mkOfActionEq (adjPairing adj) (fun Y =>
    (adj.counit.naturality (adj.counit.app Y)).symm)

/-- Let F ⊣ U be an adjunction. The target functor of its balanced two-sided bar pairing is Id_D.
Thus its component at Y pairs the degree-zero term F(UY) with Y. -/
@[simp]
theorem adjBalancedPairing_target (adj : F ⊣ U) :
    (adjBalancedPairing adj).target = 𝟭 D :=
  rfl

/-- For an adjunction F ⊣ U, the map of its balanced bar pairing equals adjPairing, the counit F∘U
→ Id_D. The balancing data therefore retain the given counit morphism at every object of D. -/
@[simp]
theorem adjBalancedPairing_pairing (adj : F ⊣ U) :
    (adjBalancedPairing adj).pairing = adjPairing adj :=
  rfl

/-- Let F ⊣ U be an adjunction and T=UF. The counit balanced pairing gives an augmented simplicial
object of D ⥤ D with underlying bar B(F,T,U) and augmentation target Id_D. Its degree-zero
augmentation is ε : F∘U → Id_D; the higher components are the balanced extension compatible
with all simplicial faces and degeneracies. -/
noncomputable def adjAugmented (adj : F ⊣ U) :
    SimplicialObject.Augmented (D ⥤ D) :=
  BalancedPairing.toSimplicialAugmented (adjBalancedPairing adj)

/-- For an adjunction F ⊣ U, the underlying simplicial object of adjAugmented equals adjBar. In
degree n it is the endofunctor Y ↦ F((UF)^n(UY)), with the canonical two-sided bar faces and
degeneracies. -/
@[simp]
theorem adjAugmented_left (adj : F ⊣ U) :
    (adjAugmented adj).left = adjBar adj :=
  rfl

/-- Let F ⊣ U be an adjunction. The target object of its augmented bar in D ⥤ D is exactly Id_D.
Thus evaluating the augmentation at Y ∈ D gives an augmented simplicial object with target Y. -/
@[simp]
theorem adjAugmented_right (adj : F ⊣ U) :
    (adjAugmented adj).right = 𝟭 D :=
  rfl

/-- For an adjunction F ⊣ U, applying the augmentation-point functor to adjAugmented gives Id_D.
This is the categorical target of the bar augmentation B(F,UF,U) → const(Id_D). -/
@[simp]
theorem adjAugmented_point_obj (adj : F ⊣ U) :
    (SimplicialObject.Augmented.point.obj (adjAugmented adj)) = 𝟭 D :=
  rfl

/-- Let F ⊣ U be an adjunction, T=UF, and n ∈ ℕ. The augmentation natural transformation at the
opposite simplex [n] equals the degree-n map of the counit balanced-pairing augmentation. Its
component at Y has source F(T^n(UY)) and target Y, and is the simplicial extension of ε_Y
compatible with the bar faces and degeneracies. -/
theorem adjAugmented_hom_app_mk (adj : F ⊣ U) (n : ℕ) :
    (adjAugmented adj).hom.app (Opposite.op (SimplexCategory.mk n)) =
      (adjBalancedPairing adj).toDataHom.app n :=
  BalancedPairing.toSimplicialAugmented_hom_app_mk _ _

/-- For an adjunction F ⊣ U, the degree-zero component of the augmented bar B(F,UF,U) →
const(Id_D) equals adjPairing, the counit F∘U → Id_D. At Y ∈ D it is ε_Y : F(UY) → Y. -/
@[simp]
theorem adjAugmented_hom_zero (adj : F ⊣ U) :
    (adjAugmented adj).hom.app (Opposite.op (SimplexCategory.mk 0)) =
      adjPairing adj := by
  change (BalancedPairing.toSimplicialAugmented (adjBalancedPairing adj)).hom.app
    (Opposite.op (SimplexCategory.mk 0)) = _
  rw [BalancedPairing.toSimplicialAugmented_hom_app_mk,
    BalancedPairing.toDataHom_app_zero, adjBalancedPairing_pairing]

end AdjAugmentation

section AdjEMComparison

variable {T : Monad C}

/-- Let T be a monad on C and S the monad induced by its free-forgetful adjunction T.free ⊣
T.forget. The forward map of the canonical monad isomorphism S≅T is a monad morphism S → T.
Its components are identities on the common underlying T-object carriers. -/
private def adjMonadHom : T.adj.toMonad ⟶ T :=
  (Adjunction.adjToMonadIso T).hom

private theorem adjMonadHom_app (X : C) :
    (adjMonadHom (T := T)).app X = 𝟙 _ := rfl

/-- Let T be a monad on C, S the monad of T.free ⊣ T.forget, h : S → T the canonical monad
morphism, and alg=(A,a) a T-algebra. Restricting scalars along h makes A an S-algebra with
action h_A ≫ a. This is the algebra used to compare the two bar constructions. -/
private def adjAlg (alg : T.Algebra) : T.adj.toMonad.Algebra :=
  (algebraFunctorOfMonadHom (adjMonadHom (T := T))).obj alg

/-- Let T be a monad on C, S the monad induced by T.free ⊣ T.forget, and h : S → T its canonical
map. The right S-module obtained by postcomposing the adjunction right module T.free with
T.forget is isomorphic to the restriction along h of the forgotten free-algebra right
T-module. Both underlying functors are T; the comparison preserves the multiplication actions. -/
private def adjRightIso :
    (adjRightModule T.adj).postcomp T.forget ≅
      (rightModuleRestrictAlongHom (D := C) adjMonadHom).obj
        (emRightModule.postcomp T.forget) := by
  refine Algebra.isoMk (Iso.refl _) ?_
  ext X
  simp only [RightModule.postcomp_functor, adjRightModule_functor, Functor.comp_obj,
    RightModule.restrictAlongHom_obj_A, emRightModule_functor, Iso.refl_hom,
    Functor.whiskerLeft_id', algebraFunctorOfMonadHom_obj_a, precompMonadHom_app,
    RightModule.action_app, Category.id_comp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.comp_map, forget_map, free_map_f,
    Category.comp_id]
  rw [adjMonadHom_app]
  change T.map (𝟙 (T.obj X)) ≫ T.forget.map (emRightModule.a.app X) =
    T.forget.map ((adjRightModule T.adj).a.app X)
  rw [Functor.map_id]
  refine (Category.id_comp _).trans ?_
  rw [Monad.forget_map, Monad.forget_map, emRightModule_action_f]
  simp only [adjRightModule_action_app]
  simp

/-- For a monad T on C, its induced free-forgetful monad S, canonical map h : S → T, and T-algebra
alg=(A,a), the constant left S-module of the restricted algebra is isomorphic to h* of the
constant left T-module of alg. The indexing category is Discrete PUnit, the carrier functor is
constant at A, and the action is h_A ≫ a. -/
private def adjLeftIso (alg : T.Algebra) :
    algebraLeftModule (adjAlg alg) ≅
      (leftModuleRestrictAlongHom (A := Discrete PUnit.{1}) adjMonadHom).obj
        (algebraLeftModule alg) := by
  refine Algebra.isoMk (Iso.refl _) ?_
  ext X
  rw [NatTrans.comp_app, NatTrans.comp_app,
    leftModuleRestrictAlongHom_obj_action_app,
    algebraLeftModule_action_app, adjMonadHom_app,
    Iso.refl_hom]
  simp only [NatTrans.id_app,
    ← LeftModule.action_app, algebraLeftModule_action_app, adjAlg,
    algebraFunctorOfMonadHom_obj_a, adjMonadHom_app]
  have hw1 : (Functor.whiskerRight (𝟙 (algebraLeftModule
      ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).obj alg)).A)
      T.adj.toMonad.toFunctor).app X = 𝟙 _ := by simp
  have hL : (Functor.whiskerRight (𝟙 (algebraLeftModule
      ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).obj alg)).A)
      T.adj.toMonad.toFunctor).app X ≫ 𝟙 _ ≫ alg.a = alg.a :=
    (congrArg (· ≫ (𝟙 _ ≫ alg.a)) hw1).trans
      ((Category.id_comp _).trans (Category.id_comp _))
  have hR : (𝟙 _ ≫ alg.a) ≫ 𝟙 _ = alg.a := by simp
  exact hL.trans hR.symm

/-- Let T be a monad on C, S its induced free-forgetful monad, and alg=(A,a) a T-algebra
restricted to S. The forgotten adjunction right S-module and the constant left S-module of
this restricted algebra have a balanced pairing to the constant functor at A. Its component is
the restricted action S(A) → A, and balancing is the algebra associativity equation. -/
private noncomputable def adjUnderlyingPairing (alg : T.Algebra) :
    BalancedPairing T.adj.toMonad ((adjRightModule T.adj).postcomp T.forget)
      (algebraLeftModule (adjAlg alg)) where
  target := BarRegularContraction.regularTarget (algebraLeftModule (adjAlg alg))
  pairing :=
    { app := fun _ => (adjAlg alg).a
      naturality := fun _ _ _ => by
        change T.adj.toMonad.map (𝟙 _) ≫ (adjAlg alg).a = (adjAlg alg).a ≫ 𝟙 _
        simp }
  balanced :=
    (isBalancedPairing_iff_action_eq (T := T.adj.toMonad)).mpr
      (fun a => (adjAlg alg).assoc)

/-- Let T be a monad on C, S its induced free-forgetful monad, and alg=(A,a) a T-algebra. Evaluate
the balanced bar of the forgotten free right S-module and the constant left S-module of the
restricted algebra at the unique discrete point. This gives an augmented simplicial object of
C with target A and zero-degree term T(A); its augmentation comes from the algebra action. -/
@[no_expose]
noncomputable def adjEvaluatedAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).obj
    (BalancedPairing.toSimplicialAugmented (adjUnderlyingPairing alg))

/-- For a monad T on C and a T-algebra alg=(A,a), the augmentation target of the evaluated bar
formed from the restricted algebra over the induced free-forgetful monad equals A. This is the
right object of adjEvaluatedAugmented(alg). -/
private theorem adjEvaluatedAugmented_point_aux (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).right = alg.A :=
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. The augmented simplicial object
adjEvaluatedAugmented(alg), obtained from the forgotten free-forgetful adjunction module and
the restricted algebra module, has augmentation target exactly A. -/
@[simp]
theorem adjEvaluatedAugmented_point (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).right = alg.A :=
  adjEvaluatedAugmented_point_aux alg

/-- For a monad T on C and a T-algebra alg=(A,a), the degree-zero term of
adjEvaluatedAugmented(alg) equals T(A). This is the free-algebra term after forgetting, before
applying its augmentation to A. -/
private theorem adjEvaluatedAugmented_obj_zero_aux (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).left.obj
      (Opposite.op (SimplexCategory.mk 0)) = T.obj alg.A :=
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. The underlying simplicial object of its
evaluated adjunction augmentation has term T(A) at the opposite simplex [0]. The target of the
augmentation is A. -/
@[simp]
theorem adjEvaluatedAugmented_obj_zero (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).left.obj
      (Opposite.op (SimplexCategory.mk 0)) = T.obj alg.A :=
  adjEvaluatedAugmented_obj_zero_aux alg

/-- For a monad T on C and a T-algebra alg, define the functor (T.Algebra ⥤ T.Algebra) → T.Algebra
by evaluating an endofunctor H at alg. It sends a natural transformation η : H → H′ to its
component η_alg. -/
noncomputable def adjEvalAlgebra (alg : T.Algebra) :
    (T.Algebra ⥤ T.Algebra) ⥤ T.Algebra :=
  (evaluation _ _).obj alg

/-- Let T be a monad on C and alg=(A,a) a T-algebra. Evaluate the augmented adjunction bar of
T.free ⊣ T.forget at alg and then apply T.forget. The result is an augmented simplicial object
of C with target A. If S is the induced adjunction monad, its degree-n term is T(S^n(A)), and
its zero-degree augmentation is the algebra action a. -/
noncomputable def adjLiteralAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj _ _
    (adjEvalAlgebra alg ⋙ T.forget)).obj (adjAugmented T.adj)

/-- For a monad T on C and a T-algebra alg, the underlying simplicial object of
adjLiteralAugmented(alg) equals the underlying augmented free-forgetful adjunction bar
followed by evaluation at alg and T.forget. Thus its object at a simplex Δ is the forgotten
value of the adjunction bar endofunctor at alg. -/
@[simp]
theorem adjLiteralAugmented_left (alg : T.Algebra) :
    (adjLiteralAugmented alg).left =
      (adjAugmented T.adj).left ⋙ (adjEvalAlgebra alg ⋙ T.forget) := by
  unfold adjLiteralAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_left]
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. The target of adjLiteralAugmented(alg),
formed by evaluating the augmented free-forgetful adjunction bar at alg and applying T.forget,
is exactly the carrier A. -/
@[simp]
theorem adjLiteralAugmented_point (alg : T.Algebra) :
    (adjLiteralAugmented alg).right = alg.A :=
  rfl

/-- For a monad T on C and a T-algebra alg=(A,a), the zero-degree term of adjLiteralAugmented(alg)
equals T(A). The construction evaluates the free-forgetful adjunction bar in T.Algebra and
then forgets its algebra structure. -/
@[simp]
theorem adjLiteralAugmented_obj_zero (alg : T.Algebra) :
    (adjLiteralAugmented alg).left.obj
      (Opposite.op (SimplexCategory.mk 0)) = T.obj alg.A :=
  rfl

/-- Let T be a monad on C and φ : alg → alg′ a T-algebra morphism. There is a natural
transformation from evaluation at alg followed by T.forget to evaluation at alg′ followed by
T.forget. At an endofunctor H of T.Algebra, its component is T.forget(H(φ)) : U(H(alg)) →
U(H(alg′)), where U=T.forget. -/
noncomputable def adjEvalForgetNatTrans {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') :
    (adjEvalAlgebra alg ⋙ T.forget) ⟶ (adjEvalAlgebra alg' ⋙ T.forget) :=
  Functor.whiskerRight ((evaluation T.Algebra T.Algebra).map φ) T.forget

/-- For a monad T on C and an algebra morphism φ : alg → alg′, forgotten evaluation naturality
gives an augmented simplicial map adjLiteralAugmented(alg) → adjLiteralAugmented(alg′). It
acts by the forgotten adjunction bar endofunctor map at each simplex and by the underlying
morphism φ.f on the augmentation targets. -/
noncomputable def adjLiteralHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    adjLiteralAugmented alg ⟶ adjLiteralAugmented alg' :=
  ((SimplicialObject.Augmented.whiskering (T.Algebra ⥤ T.Algebra) C).map
    (adjEvalForgetNatTrans φ)).app (adjAugmented T.adj)

/-- Let T be a monad on C and φ : alg → alg′ a T-algebra morphism. The right, augmentation-target
component of adjLiteralHom(φ) equals the underlying morphism φ.f : alg.A → alg′.A. This is
evaluation of the identity algebra endofunctor followed by the forgetful functor. -/
theorem adjLiteralHom_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (adjLiteralHom φ).right = φ.f :=
  rfl

/-- Let T be a monad on C, φ : alg → alg′ a T-algebra morphism, and Δ ∈ SimplexCategoryᵒᵖ. The
Δ-component of adjLiteralHom(φ) is T.forget applied to the map of φ under the Δ-endofunctor of
adjBar(T.adj). This gives the morphism between the corresponding evaluated-and-forgotten
simplicial terms. -/
theorem adjLiteralHom_left_app {alg alg' : T.Algebra} (φ : alg ⟶ alg')
    (Δ : SimplexCategoryᵒᵖ) :
    ((adjLiteralHom φ).left).app Δ =
      T.forget.map (((adjBar T.adj).obj Δ).map φ) :=
  rfl

/-- For a monad T on C and a T-algebra alg, adjLiteralHom(𝟙_alg) = 𝟙_adjLiteralAugmented(alg).
Thus the augmented bar map induced by identity evaluation is the identity on both its
simplicial object and augmentation target. -/
theorem adjLiteralHom_id (alg : T.Algebra) :
    adjLiteralHom (𝟙 alg) = 𝟙 (adjLiteralAugmented alg) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · ext Δ
    -- Restate defeq (via `adjLiteralHom_left_app`) so neither side
    -- mentions an identity projection; then two `map_id`s close it.
    change T.forget.map ((((adjAugmented T.adj).left).obj Δ).map (𝟙 alg)) =
      𝟙 _
    simp only [Functor.map_id]
  · -- Mirror `emHom_id`, chaining through the algebra identity law
    -- (never projecting `.f` off `𝟙` directly); the final link is
    -- definitional on objects.
    have e1 : (adjLiteralHom (𝟙 alg)).right = 𝟙 alg.A :=
      (adjLiteralHom_right _).trans (Algebra.id_f _)
    have e3r : (𝟙 alg.A) = 𝟙 (adjLiteralAugmented alg).right := rfl
    exact e1.trans e3r

/-- Let T be a monad on C and φ : alg₁ → alg₂, ψ : alg₂ → alg₃ algebra morphisms. Then
adjLiteralHom(φ) ≫ adjLiteralHom(ψ) = adjLiteralHom(φ ≫ ψ) as maps of augmented simplicial
objects of C. The statement includes their underlying simplicial maps and target components. -/
theorem adjLiteralHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    adjLiteralHom φ ≫ adjLiteralHom ψ = adjLiteralHom (φ ≫ ψ) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · ext Δ
    have hL12 : ((adjLiteralHom φ ≫ adjLiteralHom ψ).left).app Δ =
        (((adjLiteralHom φ).left).app Δ ≫ ((adjLiteralHom ψ).left).app Δ) :=
      rfl
    rw [hL12, adjLiteralHom_left_app, adjLiteralHom_left_app,
      adjLiteralHom_left_app, Functor.map_comp, Functor.map_comp]
    rfl
  ·     -- The stated equation would elaborate `φ.f ≫ ψ.f` against a
    -- semireducible `right`-projection type (implicit-transparency gap),
    -- so restate defeq and close by `Algebra.comp_f`.
    change φ.f ≫ ψ.f = (φ ≫ ψ).f
    exact (Algebra.comp_f φ ψ).symm

/-- For a monad T on C and a T-algebra alg, define evaluation (T.Algebra ⥤ C) → C at alg. It sends
a diagram H to H(alg) and a natural transformation to its component at alg. -/
private noncomputable def adjEvalC (alg : T.Algebra) : (T.Algebra ⥤ C) ⥤ C :=
  (evaluation _ _).obj alg

/-- Let T be a monad on C and alg a T-algebra. Evaluating an algebra-valued endofunctor at alg and
then forgetting is naturally isomorphic to first postcomposing the endofunctor with T.forget
and then evaluating at alg. Both have value U(H(alg)), and the chosen comparison has identity
components. -/
private noncomputable def adjEvalForgetIso (alg : T.Algebra) :
    (adjEvalAlgebra alg ⋙ T.forget) ≅
      (functorPostcompOuter T.forget ⋙ adjEvalC alg) :=
  Iso.refl _

/-- For a monad T on C, let S be the monad induced by T.free ⊣ T.forget. Postcompose the
adjunction right S-module by T.forget and keep the adjunction left S-module. Their two-sided
bar is a simplicial object in T.Algebra ⥤ C. Its degree-n value at an algebra Y is the
forgotten free carrier T(S^n(UY)), with U=T.forget. -/
private noncomputable def adjPostcompBar :
    SimplicialObject (T.Algebra ⥤ C) :=
  twoSidedBar T.adj.toMonad ((adjRightModule T.adj).postcomp T.forget)
    (adjLeftModule T.adj)

/-- Let T be a monad on C and alg a T-algebra. The simplicial object obtained by evaluating the
free-forgetful adjunction bar at alg and forgetting is isomorphic to evaluation at alg of the
bar whose right adjunction module is postcomposed with T.forget. This comparison uses
evaluation–postcomposition commutation and the canonical bar postcomposition isomorphism. -/
private noncomputable def adjLiteralBarIsoStep (alg : T.Algebra) :
    (adjLiteralAugmented alg).left ≅ (adjPostcompBar ⋙ adjEvalC alg) :=
  (Functor.isoWhiskerLeft (adjBar T.adj) (adjEvalForgetIso alg)) ≪≫
    (Functor.associator (adjBar T.adj) (functorPostcompOuter T.forget)
      (adjEvalC alg)).symm ≪≫
    (Functor.isoWhiskerRight
      (twoSidedBarPostcompWhiskerIso T.forget (adjRightModule T.adj)
        (adjLeftModule T.adj))
      (adjEvalC alg))

/-- For a monad T on C, a T-algebra alg, and a simplex Δ ∈ SimplexCategoryᵒᵖ, evaluation of
adjPostcompBar at alg has the same Δ-object as the underlying simplicial object of
adjEvaluatedAugmented(alg). The left module restriction preserves the algebra carrier and the
right-module postcomposition is the forgotten free functor. -/
private theorem adjPostcompEval_obj_eq (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (adjPostcompBar ⋙ adjEvalC alg).obj Δ =
      (adjEvaluatedAugmented alg).left.obj Δ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ]
  rfl

/-- Let T be a monad on C, H,H′ endofunctors of T.Algebra, η : H → H′ a natural transformation,
and alg a T-algebra. The evaluation functor at alg sends η to η_alg : H(alg) → H′(alg). -/
private theorem adjEvalAlgebra_map_app {F G : T.Algebra ⥤ T.Algebra}
    (η : F ⟶ G) (alg : T.Algebra) :
    (adjEvalAlgebra alg).map η = η.app alg :=
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. Applying T.forget to the counit of T.free ⊣
T.forget at alg gives exactly a : T(A) → A. Thus the free-forgetful counit has the algebra
structure morphism as its underlying map. -/
private theorem adjCounitForget_app (alg : T.Algebra) :
    T.forget.map ((T.adj).counit.app alg) = alg.a := by
  have hForget : T.forget.map ((T.adj).counit.app alg) =
      ((T.adj).counit.app alg).f := rfl
  have hDef : ((T.adj).counit.app alg).f =
      T.map (𝟙 (T.forget.obj alg)) ≫ alg.a := rfl
  have hMap : T.map (𝟙 (T.forget.obj alg)) = 𝟙 _ :=
    Functor.map_id _ _
  have hComp : (T.map (𝟙 (T.forget.obj alg)) ≫ alg.a) = alg.a :=
    (congrArg (· ≫ alg.a) hMap).trans (Category.id_comp _)
  exact hForget.trans (hDef.trans hComp)

/-- Let T be a monad on C, F,G : Discrete PUnit ⥤ C functors, and η : F → G a natural
transformation. The evaluation functor at the unique discrete point sends η to η at that
point. This is the component used when evaluating the constant-index bar. -/
private theorem adjEvalPoint_map_app {F G : Discrete PUnit.{1} ⥤ C}
    (η : F ⟶ G) :
    resolutionEvalPoint.map η = η.app (Discrete.mk PUnit.unit) :=
  rfl

/-- For a monad T on C and a T-algebra alg, define Discrete PUnit → T.Algebra to be the constant
functor at alg. Its unique object is sent to alg and its morphisms to identity morphisms. -/
private noncomputable def adjConstAlg (alg : T.Algebra) :
    Discrete PUnit.{1} ⥤ T.Algebra :=
  (Functor.const (Discrete PUnit.{1})).obj alg

/-- Let T be a monad on C and alg a T-algebra. Evaluation of a C-valued algebra diagram at alg is
naturally isomorphic to precomposition with the constant functor Discrete PUnit → T.Algebra at
alg followed by evaluation at the unique point. Both functors send H to H(alg), and the
comparison has identity components. -/
private noncomputable def adjEvalFactorIso (alg : T.Algebra) :
    adjEvalC alg ≅
      (functorPrecompOuter (adjConstAlg alg) ⋙ resolutionEvalPoint) :=
  Iso.refl _

/-- Let T be a monad on C, S its free-forgetful induced monad, and alg=(A,a) a T-algebra.
Precomposing the adjunction left S-module by the constant algebra functor at alg is isomorphic
to the constant left S-module of the restricted algebra. Both are functors Discrete PUnit → C
with value A and action the forgotten counit, equivalently the restricted algebra action. -/
private noncomputable def adjPrecompLeftIso (alg : T.Algebra) :
    (adjLeftModule T.adj).precomp (adjConstAlg alg) ≅
      algebraLeftModule (adjAlg alg) := by
  refine Algebra.isoMk (Iso.refl _) ?_
  ext X
  have e1 : ((adjLeftModule T.adj).precomp (adjConstAlg alg)).action.app X =
      (adjLeftModule T.adj).action.app ((adjConstAlg alg).obj X) :=
    LeftModule.precomp_action_app _ _ _
  have e2 : (adjLeftModule T.adj).action.app ((adjConstAlg alg).obj X) =
      T.forget.map (T.adj.counit.app ((adjConstAlg alg).obj X)) :=
    adjLeftModule_action_app _ _
  have e3 : T.forget.map (T.adj.counit.app ((adjConstAlg alg).obj X)) =
      T.forget.map (T.adj.counit.app alg) := rfl
  have hL : ((adjLeftModule T.adj).precomp (adjConstAlg alg)).action.app X =
      T.forget.map (T.adj.counit.app alg) :=
    e1.trans (e2.trans e3)
  have hLa : T.forget.map (T.adj.counit.app alg) = alg.a :=
    adjCounitForget_app alg
  have qA : (adjAlg (T := T) alg).a = alg.a :=
    Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
  have hR : (algebraLeftModule (adjAlg (T := T) alg)).action.app X = alg.a :=
    (algebraLeftModule_action_app _ _).trans qA
  rw [NatTrans.comp_app, NatTrans.comp_app,
    LeftModule.precomp_action_app, algebraLeftModule_action_app,
    Iso.refl_hom]
  simp only [NatTrans.id_app]
  have hW : (Functor.whiskerRight (𝟙 (adjConstAlg alg ⋙ (adjLeftModule T.adj).functor))
      T.adj.toMonad.toFunctor).app X = 𝟙 _ := by
    rw [Functor.whiskerRight_id']
    rfl
  have hLHS : (Functor.whiskerRight (𝟙 (adjConstAlg alg ⋙ (adjLeftModule T.adj).functor))
      T.adj.toMonad.toFunctor).app X ≫ (adjAlg alg).a = alg.a :=
    ((congrArg (· ≫ (adjAlg alg).a) hW).trans (Category.id_comp _)).trans qA
  have hRHS : (adjLeftModule T.adj).action.app ((adjConstAlg alg).obj X) ≫
      𝟙 _ = alg.a :=
    (Category.comp_id _).trans (hL.trans hLa)
  exact hLHS.trans hRHS.symm

/-- For a monad T on C and T-algebra alg=(A,a), the forward underlying natural transformation of
adjPrecompLeftIso(alg) is the identity of the constant functor at A. It compares the
precomposed adjunction left module with the left module of the restricted algebra. -/
@[simp]
private theorem adjPrecompLeftIso_hom_f (alg : T.Algebra) :
    (adjPrecompLeftIso (T := T) alg).hom.f = 𝟙 _ := rfl

/-- Let T be a monad on C and X ∈ C. The underlying component at X of the reflexive isomorphism of
the adjunction right module postcomposed with T.forget is the identity. Its object is the
forgotten free carrier T(X). -/
private theorem adjRightRefl_f_app (X : C) :
    (((Iso.refl ((adjRightModule T.adj).postcomp T.forget)).hom).f.app X) =
      𝟙 _ :=
  rfl

/-- For a monad T on C, T-algebra alg, and n ∈ ℕ, combine the bar precomposition isomorphism for
the constant index at alg with the left-module comparison to the restricted algebra. After
evaluation at the unique discrete point, its forward degree-n component is the identity. The
right-module comparison in this composite is reflexive. -/
private theorem adjBridgeThird_hom_app (alg : T.Algebra) (n : ℕ) :
    (Functor.isoWhiskerRight
      ((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj)) ≪≫
        (twoSidedBarIso (Iso.refl _) (adjPrecompLeftIso alg)))
      resolutionEvalPoint).hom.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  have h1 : (((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget)
        (adjLeftModule T.adj)).hom.app
      (Opposite.op (SimplexCategory.mk n))).app
      (Discrete.mk PUnit.unit)) = 𝟙 _ :=
    twoSidedBarPrecompWhiskerIso_hom_app_app_id _ _ _ _ _
  have h2 : ((barMap (Iso.refl ((adjRightModule T.adj).postcomp T.forget)).hom
        (adjPrecompLeftIso alg).hom n).app
      (Discrete.mk PUnit.unit)) = 𝟙 _ := by
    rw [barMap_app, adjRightRefl_f_app, adjPrecompLeftIso_hom_f,
      NatTrans.id_app]
    -- Term-mode close: `rw`/`simp` never match the `map_id` redex under the
    -- reducible `monadPow` unfolding, so supply fully-applied instances and
    -- assemble by congruence (cf. `hL`/`hR` below for `adjDataAug`).
    have eMap := Functor.map_id (T.adj.toMonad.monadPow n)
      ((adjConstAlg alg ⋙ (adjLeftModule T.adj).functor).obj
        { as := PUnit.unit })
    have eOut := Functor.map_id
      ((adjRightModule T.adj).postcomp T.forget).functor
      ((T.adj.toMonad.monadPow n).obj
        ((adjConstAlg alg ⋙ (adjLeftModule T.adj).functor).obj
          { as := PUnit.unit }))
    exact (((congrArg (fun m =>
        ((adjRightModule T.adj).postcomp T.forget).functor.map m ≫ 𝟙 _)
        eMap).trans
      (congrArg (fun m => m ≫ 𝟙 _) eOut)).trans (Category.comp_id _))
  have hsplit : (Functor.isoWhiskerRight
      ((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj)) ≪≫
        (twoSidedBarIso (Iso.refl _) (adjPrecompLeftIso alg)))
      resolutionEvalPoint).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
      (((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget)
        (adjLeftModule T.adj)).hom.app
      (Opposite.op (SimplexCategory.mk n))).app
      (Discrete.mk PUnit.unit)) ≫
      ((barMap (Iso.refl ((adjRightModule T.adj).postcomp T.forget)).hom
        (adjPrecompLeftIso alg).hom n).app
      (Discrete.mk PUnit.unit)) := rfl
  rw [hsplit, h1, h2]
  exact Category.id_comp _

/-- Let T be a monad on C and alg a T-algebra. The forgotten-right-module adjunction bar evaluated
at alg is isomorphic to the underlying simplicial object of adjEvaluatedAugmented(alg). The
comparison factors evaluation through the constant algebra index, then uses the bar
precomposition isomorphism and the left-module comparison with the restricted algebra. -/
private noncomputable def adjPostcompEvalBridge (alg : T.Algebra) :
    (adjPostcompBar ⋙ adjEvalC alg) ≅ (adjEvaluatedAugmented alg).left :=
  (Functor.isoWhiskerLeft adjPostcompBar (adjEvalFactorIso alg)) ≪≫
    (Functor.associator adjPostcompBar (functorPrecompOuter (adjConstAlg alg))
      resolutionEvalPoint).symm ≪≫
    (Functor.isoWhiskerRight
      ((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj)) ≪≫
        (twoSidedBarIso (Iso.refl _) (adjPrecompLeftIso alg)))
      resolutionEvalPoint)

/-- Let T be a monad on C, alg a T-algebra, and Δ a simplex. In the composite of the adjunction
bar, postcomposition by T.forget, and evaluation at alg, the inverse functor associator has
identity component at Δ. Both parenthesizations give the same forgotten evaluated bar object. -/
private theorem adjStepAssocSymm_hom_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.associator (twoSidedBar T.adj.toMonad (adjRightModule T.adj)
      (adjLeftModule T.adj)) (functorPostcompOuter T.forget)
      (adjEvalC alg)).symm.hom.app Δ =
      𝟙 _ :=
  rfl

/-- For a monad T on C, T-algebra alg, and simplex Δ, whisker the isomorphism between evaluation
followed by forgetting and postcomposition followed by evaluation by the adjunction bar. Its
forward component at Δ is the identity of the forgotten evaluated bar term. -/
private theorem adjStepWhiskerComm_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.isoWhiskerLeft (twoSidedBar T.adj.toMonad (adjRightModule T.adj)
      (adjLeftModule T.adj)) (adjEvalForgetIso alg)).hom.app Δ =
      𝟙 _ :=
  rfl

/-- Let T be a monad on C, F,G : T.Algebra ⥤ C, η : F → G, and alg a T-algebra. Evaluation at alg
sends η to its component η_alg : F(alg) → G(alg). -/
private theorem adjEvalC_map_app {F G : T.Algebra ⥤ C} (η : F ⟶ G)
    (alg : T.Algebra) :
    (adjEvalC alg).map η = η.app alg :=
  rfl

/-- For a monad T on C, a T-algebra alg, and simplex Δ, the Δ-object of the
evaluated-and-forgotten adjunction bar equals the Δ-object of the forgotten-right-module bar
evaluated at alg. This is the object equality between (adjLiteralAugmented alg).left and
adjPostcompBar followed by adjEvalC alg. -/
private theorem adjLiteralStep_obj_eq (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (adjLiteralAugmented alg).left.obj Δ =
      (adjPostcompBar ⋙ adjEvalC alg).obj Δ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ]
  rfl

/-- Let T be a monad on C, alg a T-algebra, and Δ a simplex. If h_Δ identifies the term of the
evaluated-and-forgotten bar with the evaluated postcomposed-right-module bar term, then the
forward Δ-component of adjLiteralBarIsoStep is eqToHom(h_Δ). The equality h_Δ is
adjLiteralStep_obj_eq(alg,Δ). -/
private theorem adjLiteralBarIsoStep_hom_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (adjLiteralBarIsoStep alg).hom.app Δ =
      eqToHom (adjLiteralStep_obj_eq alg _) := by
  have hdecomp : (adjLiteralBarIsoStep alg).hom =
      (Functor.isoWhiskerLeft (twoSidedBar T.adj.toMonad (adjRightModule T.adj)
        (adjLeftModule T.adj)) (adjEvalForgetIso alg)).hom ≫
      (Functor.associator (twoSidedBar T.adj.toMonad (adjRightModule T.adj)
        (adjLeftModule T.adj)) (functorPostcompOuter T.forget)
        (adjEvalC alg)).symm.hom ≫
      (Functor.isoWhiskerRight
        (twoSidedBarPostcompWhiskerIso T.forget (adjRightModule T.adj)
          (adjLeftModule T.adj))
        (adjEvalC alg)).hom := rfl
  rw [hdecomp, NatTrans.comp_app, NatTrans.comp_app,
    adjStepWhiskerComm_app, adjStepAssocSymm_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    adjEvalC_map_app,
    twoSidedBarPostcompWhiskerIso_hom_app_app_id]
  have hE : eqToHom (adjLiteralStep_obj_eq alg Δ) = 𝟙 _ := rfl
  exact ((Category.id_comp _).trans (Category.id_comp _)).trans hE.symm

/-- For a monad T on C, T-algebra alg, and simplex Δ, reassociate the forgotten-right-module
adjunction bar, precomposition by the constant index at alg, and evaluation at the unique
point. The inverse functor associator has identity component at Δ, since both
parenthesizations evaluate the same bar term at alg. -/
private theorem adjBridgeAssocSymm_hom_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.associator (twoSidedBar T.adj.toMonad
      ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj))
      (functorPrecompOuter (adjConstAlg alg))
      resolutionEvalPoint).symm.hom.app Δ =
      𝟙 _ :=
  rfl

/-- Let T be a monad on C, alg a T-algebra, and Δ a simplex. Whiskering the evaluation
factorization through the constant algebra index by the forgotten-right-module bar gives an
isomorphism with identity forward component at Δ. -/
private theorem adjBridgeWhiskerComm_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.isoWhiskerLeft (twoSidedBar T.adj.toMonad
      ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj))
      (adjEvalFactorIso alg)).hom.app Δ =
      𝟙 _ :=
  rfl

/-- For a monad T on C, T-algebra alg, and n ∈ ℕ, the forward degree-n component of
adjPostcompEvalBridge is eqToHom of the equality between the evaluated postcomposed bar term
and the term of adjEvaluatedAugmented(alg). This object equality is adjPostcompEval_obj_eq at
the opposite simplex [n]. -/
private theorem adjPostcompEvalBridge_hom_app (alg : T.Algebra) (n : ℕ) :
    (adjPostcompEvalBridge alg).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
      eqToHom (adjPostcompEval_obj_eq alg _) := by
  have hdecomp : (adjPostcompEvalBridge alg).hom =
      (Functor.isoWhiskerLeft (twoSidedBar T.adj.toMonad
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj))
        (adjEvalFactorIso alg)).hom ≫
      (Functor.associator (twoSidedBar T.adj.toMonad
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj))
        (functorPrecompOuter (adjConstAlg alg))
        resolutionEvalPoint).symm.hom ≫
      (Functor.isoWhiskerRight
        ((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
          ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj)) ≪≫
          (twoSidedBarIso (Iso.refl _) (adjPrecompLeftIso alg)))
        resolutionEvalPoint).hom := rfl
  rw [hdecomp, NatTrans.comp_app, NatTrans.comp_app,
    adjBridgeWhiskerComm_app, adjBridgeAssocSymm_hom_app]
  -- Stop rewriting here: the goal now carries `𝟙`-pinned links, and any
  -- further `rw` motive over the mixed composite would need `no_expose`
  -- unfolding. Assemble the rest in term mode at default transparency.
  have l3 : (Functor.isoWhiskerRight
      ((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj)) ≪≫
        (twoSidedBarIso (Iso.refl _) (adjPrecompLeftIso alg)))
      resolutionEvalPoint).hom.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ :=
    adjBridgeThird_hom_app alg n
  have hE : eqToHom (adjPostcompEval_obj_eq alg
      (Opposite.op (SimplexCategory.mk n))) = 𝟙 _ := rfl
  exact ((congrArg (fun c => 𝟙 _ ≫ 𝟙 _ ≫ c) l3).trans
    (((Category.id_comp _).trans (Category.id_comp _)).trans hE.symm))

/-- Let T be a monad on C, alg a T-algebra, and Δ ∈ SimplexCategoryᵒᵖ. The Δ-term of
adjLiteralAugmented(alg), obtained by evaluating and forgetting the adjunction bar, equals the
Δ-term of adjEvaluatedAugmented(alg), obtained from the restricted algebra module and
forgotten right module. -/
theorem adjLiteralBar_obj_eq (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (adjLiteralAugmented alg).left.obj Δ =
      (adjEvaluatedAugmented alg).left.obj Δ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ]
  rfl

/-- For a monad T on C and a T-algebra alg, the underlying simplicial objects of
adjLiteralAugmented(alg) and adjEvaluatedAugmented(alg) are isomorphic. The comparison first
commutes forgetting with evaluation of the bar and then identifies constant-index
precomposition with the restricted algebra left module. -/
@[no_expose]
noncomputable def adjLiteralBarIso (alg : T.Algebra) :
    (adjLiteralAugmented alg).left ≅ (adjEvaluatedAugmented alg).left :=
  adjLiteralBarIsoStep alg ≪≫ adjPostcompEvalBridge alg

/-- Let T be a monad on C, alg a T-algebra, and n ∈ ℕ. The forward degree-n component of
adjLiteralBarIso(alg) is eqToHom of adjLiteralBar_obj_eq at the opposite simplex [n]. Thus the
simplicial comparison uses the specified equality between the two degree objects. -/
theorem adjLiteralBarIso_hom_app (alg : T.Algebra) (n : ℕ) :
    (adjLiteralBarIso alg).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
      eqToHom (adjLiteralBar_obj_eq alg _) := by
  have hcomp : (adjLiteralBarIso alg).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
      (adjLiteralBarIsoStep alg).hom.app
        (Opposite.op (SimplexCategory.mk n)) ≫
        (adjPostcompEvalBridge alg).hom.app
          (Opposite.op (SimplexCategory.mk n)) := rfl
  simp only [hcomp, adjLiteralBarIsoStep_hom_app, adjPostcompEvalBridge_hom_app,
    eqToHom_trans]

/-- For a monad T on C and a T-algebra alg, the zero-degree augmentation of
adjEvaluatedAugmented(alg) equals the action of alg restricted to the induced free-forgetful
monad. Its source is the restricted free carrier and its target is alg.A. -/
private theorem adjEvaluatedAugmented_hom_zero_aux (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = (adjAlg alg).a := by
  unfold adjEvaluatedAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    BalancedPairing.toSimplicialAugmented_hom_app_mk,
    BalancedPairing.toDataHom_app_zero]
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. Identify the zero-degree term of
adjEvaluatedAugmented(alg) with T(A) and its augmentation target with A using the stated
object equalities e_0 and e_A. Then eqToHom(e_0.symm) ≫ ε_0 ≫ eqToHom(e_A) = a, where ε_0 is
its zero-degree augmentation. This specifies the source and target transports of the action
equation. -/
theorem adjEvaluatedAugmented_hom_zero (alg : T.Algebra) :
    eqToHom (adjEvaluatedAugmented_obj_zero alg).symm ≫
      (adjEvaluatedAugmented alg).hom.app
        (Opposite.op (SimplexCategory.mk 0)) ≫
      eqToHom (adjEvaluatedAugmented_point alg) = alg.a := by
  have hAux : (adjEvaluatedAugmented (T := T) alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = (adjAlg (T := T) alg).a :=
    adjEvaluatedAugmented_hom_zero_aux alg
  have qA : (adjAlg (T := T) alg).a = alg.a :=
    Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
  have hE1 : eqToHom (adjEvaluatedAugmented_obj_zero (T := T) alg).symm =
      𝟙 (T.obj alg.A) := rfl
  have hE2 : eqToHom (adjEvaluatedAugmented_point (T := T) alg) =
      𝟙 alg.A := rfl
  -- Single term-mode close: every `rw` motive over the mixed
  -- transport/augmentation composite would need `no_expose` unfolding.
  -- (`≫` is right-associative, so no `assoc` step is needed.)
  have hclose : (𝟙 _ ≫ alg.a ≫ 𝟙 _) = alg.a :=
    ((congrArg (fun f => 𝟙 _ ≫ f) (Category.comp_id alg.a)).trans
      (Category.id_comp alg.a))
  exact (congrArg (fun m => eqToHom
      (adjEvaluatedAugmented_obj_zero (T := T) alg).symm ≫ m ≫
      eqToHom (adjEvaluatedAugmented_point (T := T) alg))
      (hAux.trans qA)).trans
    (((congrArg (fun e => e ≫ alg.a ≫
      eqToHom (adjEvaluatedAugmented_point (T := T) alg)) hE1).trans
      (congrArg (fun e => 𝟙 _ ≫ alg.a ≫ e) hE2)).trans hclose)

/-- Let T be a monad on C, S its free-forgetful induced monad, n ∈ ℕ, and X ∈ C. Applying T.forget
to the iterated right S-action of the adjunction right module equals the iterated action of
that module postcomposed with T.forget. Both maps go from the forgotten degree-(n+1) power
object to its degree-n object. -/
private theorem adjRightPowForget_agree (n : ℕ) (X : C) :
    T.forget.map (rightActionPow T.adj.toMonad (adjRightModule T.adj) n X) =
      rightActionPow T.adj.toMonad
        ((adjRightModule T.adj).postcomp T.forget) n X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => exact ih _

/-- Let T be a monad on C, alg a T-algebra, and n ∈ ℕ. Apply T.forget to the first face d_0 of the
free-forgetful adjunction bar evaluated at alg. It equals the first face of the bar with
forgotten right module and restricted constant algebra left module, evaluated at the unique
discrete point. Both maps go from degree n+1 to degree n. -/
private theorem adjDataFace_agree (alg : T.Algebra) (n : ℕ) :
    T.forget.map (((((barData T.adj.toMonad (adjRightModule T.adj)
        (adjLeftModule T.adj)).δ (0 : Fin (n + 2))).app alg))) =
      ((((barData T.adj.toMonad ((adjRightModule T.adj).postcomp T.forget)
        (algebraLeftModule (adjAlg alg))).δ (0 : Fin (n + 2))).app
          ⟨PUnit.unit⟩)) := by
  rw [barData_δ_app, barData_δ_app]
  have h0 : ((0 : Fin (n + 2)).val = 0) := rfl
  unfold barFaceApp
  rw [dite_eq_left h0]
  exact adjRightPowForget_agree n _

/-- Let T be a monad on C, alg a T-algebra, and n ∈ ℕ. The forgotten degree-n component of the
counit balanced augmentation of the free-forgetful adjunction bar at alg equals the degree-n
component of adjUnderlyingPairing(alg), evaluated at the unique discrete point. Both have the
same bar term as source and alg.A as target. -/
private theorem adjDataForget_agree (alg : T.Algebra) (n : ℕ) :
    T.forget.map ((((adjBalancedPairing T.adj).toDataHom.app n).app alg)) =
      ((((adjUnderlyingPairing alg).toDataHom.app n).app
        ⟨PUnit.unit⟩)) := by
  induction n with
  | zero =>
    have hLp : ((adjUnderlyingPairing (T := T) alg).pairing).app
        ⟨PUnit.unit⟩ = (adjAlg alg).a := rfl
    have qA : (adjAlg (T := T) alg).a = alg.a :=
      Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
    simp only [BalancedPairing.toDataHom_app_zero, adjBalancedPairing_pairing,
      adjPairing_app]
    exact (adjCounitForget_app alg).trans (hLp.trans qA).symm
  | succ n ih =>
    have eL : T.forget.map ((((adjBalancedPairing T.adj).toDataHom.app
        (n + 1))).app alg) =
        T.forget.map (((((barData T.adj.toMonad (adjRightModule T.adj)
          (adjLeftModule T.adj)).δ (0 : Fin (n + 2))).app alg))) ≫
          T.forget.map ((((adjBalancedPairing T.adj).toDataHom.app n).app
            alg)) := by
      rw [BalancedPairing.toDataHom_app_succ, NatTrans.comp_app]
      exact Functor.map_comp _ _ _
    have eR : ((((adjUnderlyingPairing alg).toDataHom.app (n + 1))).app
        ⟨PUnit.unit⟩) =
        (((((barData T.adj.toMonad ((adjRightModule T.adj).postcomp T.forget)
          (algebraLeftModule (adjAlg alg))).δ (0 : Fin (n + 2))).app
            ⟨PUnit.unit⟩))) ≫
        ((((adjUnderlyingPairing alg).toDataHom.app n).app
          ⟨PUnit.unit⟩)) := by
      rw [BalancedPairing.toDataHom_app_succ, NatTrans.comp_app]
    -- Single term-mode close: after the face/consensus rewrites the goal
    -- is `X ≫ Y = X ≫ Y`, which neither `rw` nor `simp` discharge here,
    -- so assemble from the two one-sided equations by congruence.
    exact eL.trans ((congrArg (· ≫ _) (adjDataFace_agree alg n)).trans
      ((congrArg (_ ≫ ·) ih).trans eR.symm))

/-- For a monad T on C, T-algebra alg, and n ∈ ℕ, the augmentation component of
adjLiteralAugmented(alg) at the opposite simplex [n] equals that of
adjEvaluatedAugmented(alg). This compares evaluation-and-forgetting with the augmentation from
the restricted algebra module and forgotten right module. -/
private theorem adjLiteralHomAgree_app (alg : T.Algebra) (n : ℕ) :
    (adjLiteralAugmented alg).hom.app (Opposite.op (SimplexCategory.mk n)) =
      (adjEvaluatedAugmented alg).hom.app
        (Opposite.op (SimplexCategory.mk n)) := by
  unfold adjLiteralAugmented adjEvaluatedAugmented adjAugmented
  simp only [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    BalancedPairing.toSimplicialAugmented_hom_app_mk]
  change T.forget.map ((adjEvalAlgebra alg).map
      ((adjBalancedPairing T.adj).toDataHom.app n)) =
    resolutionEvalPoint.map ((adjUnderlyingPairing alg).toDataHom.app n)
  rw [adjEvalAlgebra_map_app, adjEvalPoint_map_app]
  exact adjDataForget_agree alg n

/-- Let T be a monad on C and alg a T-algebra. The simplicial comparison adjLiteralBarIso(alg),
together with the identity on the augmentation target alg.A, defines an isomorphism
adjLiteralAugmented(alg) ≅ adjEvaluatedAugmented(alg). The componentwise augmentation
agreement makes it an isomorphism of augmented simplicial objects. -/
@[no_expose]
noncomputable def adjLiteralIso (alg : T.Algebra) :
    adjLiteralAugmented alg ≅ adjEvaluatedAugmented alg :=
  Comma.isoMk (adjLiteralBarIso alg) (Iso.refl _) (by
    ext Δ
    simp only [NatTrans.comp_app, Functor.id_map]
    have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
      obtain ⟨d⟩ := Δ
      exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
    rw [hΔ, adjLiteralHomAgree_app]
    have h1 := adjLiteralBarIso_hom_app alg (Opposite.unop Δ).len
    rw [h1]
    -- Term-mode close: `rw` cannot form motives over the opaque
    -- mixed `𝟙`-then-augmentation composites, so bridge with `congrArg`
    -- and the identity laws at default transparency.
    have hE : eqToHom (adjLiteralBar_obj_eq alg
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) = 𝟙 _ := rfl
    have hR : ((SimplicialObject.const C).map
        (Iso.refl (adjLiteralAugmented alg).right).hom).app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) = 𝟙 _ := by
      simp only [Iso.refl_hom, Functor.map_id, NatTrans.id_app]
    exact ((congrArg (fun e => e ≫ (adjEvaluatedAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) hE).trans
      (Category.id_comp _)).trans
      (((congrArg (fun e => (adjEvaluatedAugmented alg).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) ≫ e) hR).trans
        (Category.comp_id _)).symm))

/-- For a monad T on C and a T-algebra alg=(A,a), the zero-degree augmentation of
adjLiteralAugmented(alg) is exactly a : T(A) → A. It is the forgotten counit of the
free-forgetful adjunction evaluated at alg. -/
@[simp]
theorem adjLiteralAugmented_hom_zero (alg : T.Algebra) :
    (adjLiteralAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = alg.a := by
  have hWhisk : (adjLiteralAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) =
      (adjEvalAlgebra alg ⋙ T.forget).map ((adjAugmented T.adj).hom.app
        (Opposite.op (SimplexCategory.mk 0))) := by
    unfold adjLiteralAugmented
    rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk]
  have hAug : (adjAugmented T.adj).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = adjPairing T.adj :=
    adjAugmented_hom_zero _
  have hComp : (adjEvalAlgebra alg ⋙ T.forget).map (adjPairing T.adj) =
      T.forget.map ((adjEvalAlgebra alg).map (adjPairing T.adj)) :=
    Functor.comp_map _ _ _
  have hEval : (adjEvalAlgebra alg).map (adjPairing T.adj) =
      (adjPairing T.adj).app alg :=
    adjEvalAlgebra_map_app _ _
  have hPair : (adjPairing T.adj).app alg = (T.adj).counit.app alg :=
    adjPairing_app _ _
  have hEvalPair : (adjEvalAlgebra alg).map (adjPairing T.adj) =
      (T.adj).counit.app alg :=
    hEval.trans hPair
  have hForgetEval : T.forget.map ((adjEvalAlgebra alg).map (adjPairing T.adj)) =
      alg.a :=
    (congrArg T.forget.map hEvalPair).trans (adjCounitForget_app alg)
  have hKPair : (adjEvalAlgebra alg ⋙ T.forget).map (adjPairing T.adj) = alg.a :=
    hComp.trans hForgetEval
  exact hWhisk.trans ((congrArg _ hAug).trans hKPair)

/-- For a monad T on C and a T-algebra alg=(A,a), the forward map of adjLeftIso(alg) has identity
underlying natural transformation on the constant functor at A. This compares the left module
of the restricted algebra over the induced monad with the restriction of its left T-module. -/
@[simp]
private theorem adjLeftIso_hom_f (alg : T.Algebra) :
    (adjLeftIso (T := T) alg).hom.f = 𝟙 _ := rfl

/-- Let T be a monad on C, S its induced free-forgetful monad, h : S → T the canonical map, and
alg a T-algebra. Compose the right and left module isomorphism bar map with the bar change
along h to obtain c on the corresponding simplicial data. Then c followed by the
Eilenberg–Moore underlying augmentation equals the restricted-adjunction augmentation followed
by the constant identity target map. Thus the comparison preserves the action pairing. -/
private theorem adjDataAug_w (alg : T.Algebra) :
    (barDataHom (adjRightIso (T := T)).hom (adjLeftIso alg).hom ≫
          barChangeDataHom (adjMonadHom (T := T))
            (emRightModule.postcomp T.forget)
            (algebraLeftModule alg)) ≫ (emUnderlyingPairing alg).toDataHom =
        (adjUnderlyingPairing alg).toDataHom ≫
          SimplicialObject.Data.constDataHom (𝟙 _) := by
  apply SimplicialObject.Data.hom_eq_of_app_zero_eq
  simp only [SimplicialObject.comp_app,
    BalancedPairing.toDataHom_app_zero,
    SimplicialObject.Data.constDataHom_app]
  ext X
  -- Term-mode: `rfl`/`exact` bridge the `barObj`/`barData.obj` gap (default
  -- transparency); every propositional step below elaborates a closed term,
  -- so no `rw` motive is ever built over the bridged composite.
  have m1 (Z : C) : (monadPow T.adj.toMonad 0).map (𝟙 Z) = 𝟙 Z := by simp
  have m2 (Z : C) : (monadPowHom (adjMonadHom (T := T)) 0).app Z = 𝟙 Z :=
    monadPowHom_zero_app _ Z
  have eL : ((((barDataHom adjRightIso.hom (adjLeftIso alg).hom).app 0 ≫
        (barChangeDataHom adjMonadHom (emRightModule.postcomp T.forget)
          (algebraLeftModule alg)).app 0) ≫
      (emUnderlyingPairing alg).pairing)).app X
      = (((((adjRightModule T.adj).postcomp T.forget).functor.map
        ((monadPow T.adj.toMonad 0).map
          (𝟙 ((algebraLeftModule (adjAlg alg)).functor.obj X))) ≫ 𝟙 _) ≫
        ((emRightModule.postcomp T.forget).functor.map
          ((monadPowHom (adjMonadHom (T := T)) 0).app _))) ≫ alg.a) := rfl
  have eR : (((adjUnderlyingPairing alg).pairing ≫ 𝟙 _)).app X
      = ((adjAlg alg).a ≫ 𝟙 _) := rfl
  have r1 : (((adjRightModule T.adj).postcomp T.forget).functor.map
      ((monadPow T.adj.toMonad 0).map
        (𝟙 ((algebraLeftModule (adjAlg alg)).functor.obj X)))) = 𝟙 _ :=
    (congrArg _ (m1 _)).trans (Functor.map_id _ _)
  have r2 : ((emRightModule.postcomp T.forget).functor.map
      ((monadPowHom (adjMonadHom (T := T)) 0).app
        ((algebraLeftModule (adjAlg alg)).functor.obj X))) = 𝟙 _ :=
    (congrArg _ (m2 _)).trans (Functor.map_id _ _)
  have qA : (adjAlg alg).a = alg.a :=
    Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
  have s1 : ((((adjRightModule T.adj).postcomp T.forget).functor.map
      ((monadPow T.adj.toMonad 0).map
        (𝟙 ((algebraLeftModule (adjAlg alg)).functor.obj X))) ≫ 𝟙 _)) = 𝟙 _ :=
    (congrArg (· ≫ 𝟙 _) r1).trans (Category.id_comp _)
  have nL : (((((adjRightModule T.adj).postcomp T.forget).functor.map
        ((monadPow T.adj.toMonad 0).map
          (𝟙 ((algebraLeftModule (adjAlg alg)).functor.obj X))) ≫ 𝟙 _) ≫
        ((emRightModule.postcomp T.forget).functor.map
          ((monadPowHom (adjMonadHom (T := T)) 0).app _))) ≫ alg.a) = alg.a :=
    (congrArg (· ≫ alg.a)
      ((congrArg (· ≫ ((emRightModule.postcomp T.forget).functor.map
        ((monadPowHom (adjMonadHom (T := T)) 0).app _))) s1).trans
        (Category.id_comp _))).trans
      ((congrArg (· ≫ alg.a) r2).trans (Category.id_comp _))
  have nR : ((adjAlg alg).a ≫ 𝟙 _) = alg.a :=
    (congrArg (· ≫ 𝟙 _) qA).trans (Category.comp_id _)
  exact eL.trans (nL.trans (nR.symm.trans eR.symm))

/-- For a monad T on C and T-algebra alg, the module-comparison bar map followed by bar change
along the canonical induced-monad morphism defines a map of augmented simplicial data from
adjUnderlyingPairing(alg) to emUnderlyingPairing(alg). Its map on augmentation targets is the
identity of the constant algebra carrier. -/
private noncomputable def adjDataAugHom (alg : T.Algebra) :
    (adjUnderlyingPairing alg).toAugmented ⟶
      (emUnderlyingPairing alg).toAugmented where
  left :=
    barDataHom (adjRightIso (T := T)).hom (adjLeftIso alg).hom ≫
      barChangeDataHom (adjMonadHom (T := T))
        (emRightModule.postcomp T.forget) (algebraLeftModule alg)
  right := 𝟙 _
  w := adjDataAug_w alg

/-- Let T be a monad on C and alg a T-algebra. The canonical induced-monad map, together with the
right and left module comparisons, gives an augmented simplicial morphism
adjEvaluatedAugmented(alg) → emUnderlyingAugmented(alg). It is the evaluated map of augmented
bar data, and its target component preserves the algebra carrier. -/
@[no_expose]
noncomputable def adjToEMComparison (alg : T.Algebra) :
    adjEvaluatedAugmented alg ⟶ emUnderlyingAugmented alg :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).map
    (SimplicialObject.Data.Augmented.toSimplicialFunctor.map (adjDataAugHom alg))

/-- For a monad T on C and a T-algebra alg, the simplicial component of adjToEMComparison(alg) is
obtained by evaluating the composite of the two-sided bar isomorphism of the canonical right
and left module comparisons and the bar-change morphism along the induced-monad map.
Evaluation is at the unique discrete point. -/
@[simp]
private theorem adjToEMComparison_left (alg : T.Algebra) :
    (adjToEMComparison alg).left =
      Functor.whiskerRight
        ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg)).hom ≫
          barChangeHom (adjMonadHom (T := T)) _ _) resolutionEvalPoint := by
  simp only [adjToEMComparison, adjDataAugHom, twoSidedBarIso_hom]
  rfl

/-- Let T be a monad on C and alg a T-algebra. The augmentation-target component of
adjToEMComparison(alg) equals evaluation at the unique discrete point of the target map of
adjDataAugHom(alg). That target map is the identity of the constant algebra carrier. -/
@[simp]
private theorem adjToEMComparison_right (alg : T.Algebra) :
    (adjToEMComparison alg).right =
      resolutionEvalPoint.map (adjDataAugHom alg).right :=
  Eq.trans
    (SimplicialObject.Augmented.whiskeringObj_map_right _ _)
    (congrArg resolutionEvalPoint.map
      (SimplicialObject.Data.Augmented.toSimplicialFunctor_map_right _))

/-- For a monad T on C and a T-algebra alg, let γ be adjToEMComparison(alg). Let e_adj and e_em
identify its source and target augmentation objects with alg.A. Then γ.right ≫ eqToHom(e_em) =
eqToHom(e_adj). Thus the target map is the identity of the algebra carrier after these
specified object transports. -/
theorem adjToEMComparison_right_eqToHom (alg : T.Algebra) :
    (adjToEMComparison alg).right ≫
      eqToHom (emUnderlyingAugmented_point alg) =
      eqToHom (adjEvaluatedAugmented_point alg) := by
  have hR : (adjToEMComparison (T := T) alg).right =
      resolutionEvalPoint.map (adjDataAugHom (T := T) alg).right :=
    adjToEMComparison_right alg
  have hId : (adjDataAugHom (T := T) alg).right = 𝟙 _ := rfl
  have hMap : resolutionEvalPoint.map (adjDataAugHom (T := T) alg).right =
      𝟙 (adjEvaluatedAugmented (T := T) alg).right :=
    (congrArg resolutionEvalPoint.map hId).trans (Functor.map_id _ _)
  have hRightEq : (adjToEMComparison (T := T) alg).right =
      𝟙 (adjEvaluatedAugmented (T := T) alg).right :=
    hR.trans hMap
  have hStep1 : ((adjToEMComparison (T := T) alg).right ≫
      eqToHom (emUnderlyingAugmented_point alg)) =
      (𝟙 (adjEvaluatedAugmented (T := T) alg).right ≫
        eqToHom (emUnderlyingAugmented_point alg)) :=
    congrArg (· ≫ eqToHom (emUnderlyingAugmented_point alg)) hRightEq
  have hStep2 : (𝟙 (adjEvaluatedAugmented (T := T) alg).right ≫
      eqToHom (emUnderlyingAugmented_point alg)) =
      eqToHom (adjEvaluatedAugmented_point alg) :=
    Category.id_comp _ |>.trans (by rfl)
  exact hStep1.trans hStep2

/-- Let T be a monad on C and alg=(A,a) a T-algebra. The zero-degree object of
adjEvaluatedAugmented(alg) equals the zero-degree object of emUnderlyingAugmented(alg). Both
are the forgotten free carrier T(A). -/
private theorem adjToEMComparison_obj_zero_aux (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).left.obj
      (Opposite.op (SimplexCategory.mk 0)) =
      (emUnderlyingAugmented alg).left.obj
        (Opposite.op (SimplexCategory.mk 0)) :=
  rfl

/-- For a monad T on C and a T-algebra alg, the simplicial objects underlying
adjEvaluatedAugmented(alg) and emUnderlyingAugmented(alg) have equal terms at the opposite
simplex [0]. This is the source–target object identification used for the zero-degree
comparison map. -/
theorem adjToEMComparison_obj_zero (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).left.obj
      (Opposite.op (SimplexCategory.mk 0)) =
      (emUnderlyingAugmented alg).left.obj
        (Opposite.op (SimplexCategory.mk 0)) :=
  adjToEMComparison_obj_zero_aux alg

/-- Let T be a monad on C and alg a T-algebra. The zero-degree simplicial component of
adjToEMComparison(alg) equals eqToHom of the equality between its source and target
zero-degree terms. This equality is adjToEMComparison_obj_zero(alg). -/
private theorem adjToEMComparison_left_zero_aux (alg : T.Algebra) :
    ((adjToEMComparison alg).left).app
      (Opposite.op (SimplexCategory.mk 0)) =
      eqToHom (adjToEMComparison_obj_zero alg) := by
  have hEq : eqToHom (adjToEMComparison_obj_zero (T := T) alg) = 𝟙 _ := rfl
  have hFL0 : (((adjLeftIso (T := T) alg).hom.f).app
      (Discrete.mk PUnit.unit)) = 𝟙 _ := rfl
  have hFR0 : ∀ (X : C), (((adjRightIso (T := T)).hom.f).app X) = 𝟙 _ :=
    fun X => rfl
  have hPowHom0 : ∀ (X : C),
      (monadPowHom (adjMonadHom (T := T)) 0).app X = 𝟙 X :=
    fun X => rfl
  have hPowMap : ∀ (X : C),
      (monadPow T.adj.toMonad 0).map (𝟙 X) = 𝟙 X :=
    fun X => rfl
  have hPoint : (barMap (adjRightIso (T := T)).hom
      (adjLeftIso (T := T) alg).hom 0 ≫
      barChangeMap (adjMonadHom (T := T)) (emRightModule.postcomp T.forget)
        (algebraLeftModule alg) 0).app (Discrete.mk PUnit.unit) = 𝟙 _ := by
    -- Term-mode: `rfl` bridges the `barMap`/`barChangeMap` unfolding gap
    -- (default transparency; `rw`/`simp` motives re-check at implicit
    -- transparency and misfire here). Every propositional step below is a
    -- closed `congrArg`/`trans` over morphisms in `C`.
    have eL : (barMap (adjRightIso (T := T)).hom
        (adjLeftIso (T := T) alg).hom 0 ≫
        barChangeMap (adjMonadHom (T := T)) (emRightModule.postcomp T.forget)
          (algebraLeftModule alg) 0).app (Discrete.mk PUnit.unit)
        = (((((adjRightModule T.adj).postcomp T.forget).functor.map
            ((monadPow T.adj.toMonad 0).map
              (((adjLeftIso (T := T) alg).hom.f).app
                (Discrete.mk PUnit.unit))) ≫
            (((adjRightIso (T := T)).hom.f).app _)) ≫
          (emRightModule.postcomp T.forget).functor.map
            ((monadPowHom (adjMonadHom (T := T)) 0).app
              ((algebraLeftModule alg).functor.obj
                (Discrete.mk PUnit.unit))))) := rfl
    have q1 : (monadPow T.adj.toMonad 0).map
        (((adjLeftIso (T := T) alg).hom.f).app
          (Discrete.mk PUnit.unit)) = 𝟙 _ :=
      (congrArg ((monadPow T.adj.toMonad 0).map) hFL0).trans (hPowMap _)
    have qR : (((adjRightModule T.adj).postcomp T.forget).functor.map
        ((monadPow T.adj.toMonad 0).map
          (((adjLeftIso (T := T) alg).hom.f).app
            (Discrete.mk PUnit.unit)))) = 𝟙 _ :=
      (congrArg (((adjRightModule T.adj).postcomp T.forget).functor.map)
        q1).trans (Functor.map_id _ _)
    have sMid : ((adjRightModule T.adj).postcomp T.forget).functor.map
          ((monadPow T.adj.toMonad 0).map
            (((adjLeftIso (T := T) alg).hom.f).app (Discrete.mk PUnit.unit)))
          ≫ (((adjRightIso (T := T)).hom.f).app ((monadPow T.adj.toMonad 0).obj
            (((leftModuleRestrictAlongHom (adjMonadHom (T := T))).obj
              (algebraLeftModule alg)).A.obj
              (Discrete.mk PUnit.unit)))) = 𝟙 _ :=
      ((congrArg (· ≫ _) qR).trans (congrArg (𝟙 _ ≫ ·) (hFR0 _))).trans
        (Category.comp_id _)
    rw [sMid] at eL
    have hPH : (monadPowHom (adjMonadHom (T := T)) 0).app
        ((algebraLeftModule alg).functor.obj
          (Discrete.mk PUnit.unit)) = 𝟙 _ :=
      hPowHom0 _
    rw [hPH] at eL
    have hRem : ((emRightModule.postcomp T.forget).functor.map
        (𝟙 ((monadPow T.adj.toMonad 0).obj
          ((algebraLeftModule alg).functor.obj (Discrete.mk PUnit.unit))))) =
        𝟙 _ :=
      Functor.map_id _ _
    have hStep : (𝟙 (((adjRightModule T.adj).postcomp T.forget).functor.obj
          ((monadPow T.adj.toMonad 0).obj
            ((algebraLeftModule (adjAlg alg)).A.obj (Discrete.mk PUnit.unit))))
          ≫ (emRightModule.postcomp T.forget).functor.map
            (𝟙 ((monadPow T.adj.toMonad 0).obj
              ((algebraLeftModule alg).functor.obj
                (Discrete.mk PUnit.unit))))) =
        𝟙 (((adjRightModule T.adj).postcomp T.forget).functor.obj
          ((monadPow T.adj.toMonad 0).obj
            ((algebraLeftModule (adjAlg alg)).A.obj (Discrete.mk PUnit.unit)))) :=
      ((congrArg (𝟙 _ ≫ ·) hRem).trans (Category.comp_id _))
    exact eL.trans hStep
  have hApp : ((adjToEMComparison (T := T) alg).left).app
      (Opposite.op (SimplexCategory.mk 0)) = 𝟙 _ := by
    have e1 : ((adjToEMComparison (T := T) alg).left).app
        (Opposite.op (SimplexCategory.mk 0)) =
        resolutionEvalPoint.map (barMap (adjRightIso (T := T)).hom
          ((adjLeftIso (T := T) alg).hom) 0 ≫
          barChangeMap (adjMonadHom (T := T))
          (emRightModule.postcomp T.forget) (algebraLeftModule alg) 0) := by
      rw [adjToEMComparison_left]
      have hInner : (((twoSidedBarIso (adjRightIso (T := T))
          (adjLeftIso alg)).hom ≫
          barChangeHom (adjMonadHom (T := T)) _ _).app
          (Opposite.op (SimplexCategory.mk 0)))
          = (barMap (adjRightIso (T := T)).hom
            ((adjLeftIso (T := T) alg).hom) 0 ≫
            barChangeMap (adjMonadHom (T := T))
            (emRightModule.postcomp T.forget) (algebraLeftModule alg) 0) :=
        rfl
      exact congrArg resolutionEvalPoint.map hInner
    have eEval : resolutionEvalPoint.map (barMap (adjRightIso (T := T)).hom
        ((adjLeftIso (T := T) alg).hom) 0 ≫
        barChangeMap (adjMonadHom (T := T))
        (emRightModule.postcomp T.forget) (algebraLeftModule alg) 0) =
        (barMap (adjRightIso (T := T)).hom (adjLeftIso (T := T) alg).hom 0 ≫
          barChangeMap (adjMonadHom (T := T)) (emRightModule.postcomp T.forget)
            (algebraLeftModule alg) 0).app (Discrete.mk PUnit.unit) := rfl
    exact e1.trans (eEval.trans hPoint)
  exact hApp.trans hEq.symm

/-- For a monad T on C and a T-algebra alg, the degree-zero component of the simplicial map
adjToEMComparison(alg) is eqToHom(adjToEMComparison_obj_zero(alg)). Hence the comparison is
the specified identity transport between the two zero-degree free carriers. -/
theorem adjToEMComparison_left_zero (alg : T.Algebra) :
    ((adjToEMComparison alg).left).app
      (Opposite.op (SimplexCategory.mk 0)) =
      eqToHom (adjToEMComparison_obj_zero alg) :=
  adjToEMComparison_left_zero_aux alg

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The constant augmentation target
diagrams of adjUnderlyingPairing(alg) and adjUnderlyingPairing(alg′) have a natural
transformation whose component at every discrete point is φ.f : alg.A → alg′.A. -/
private noncomputable def adjUnderlyingTargetHom {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') :
    (adjUnderlyingPairing alg).target ⟶ (adjUnderlyingPairing alg').target where
  app _ := φ.f
  naturality _ _ _ := by
    change (𝟙 alg.A) ≫ φ.f = φ.f ≫ (𝟙 alg'.A)
    simp

/-- For a monad T on C, an algebra morphism φ : alg → alg′, and a point X ∈ Discrete PUnit,
adjUnderlyingTargetHom(φ)_X = φ.f. This identifies the component of the natural map between
the constant algebra-carrier targets. -/
@[simp]
private theorem adjUnderlyingTargetHom_app {alg alg' : T.Algebra} (φ : alg ⟶ alg')
    (X : Discrete PUnit.{1}) :
    ((adjUnderlyingTargetHom (T := T) φ).app X) = φ.f :=
  rfl

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The degree-zero bar map with
identity on the forgotten right module and the restricted algebra left-module map satisfies
b_0(φ) ≫ pairing_alg′ = pairing_alg ≫ target(φ). The target map is constant at φ.f, and the
equality is the algebra-morphism compatibility with the action. -/
private theorem adjUnderlying_hq {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    barMap (𝟙 ((adjRightModule T.adj).postcomp T.forget))
        (algebraLeftModuleHom ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) 0 ≫
        (adjUnderlyingPairing alg').pairing =
      (adjUnderlyingPairing alg).pairing ≫ adjUnderlyingTargetHom φ := by
  ext X
  -- Term-mode bridge: every link below is `rfl` at default transparency
  -- (`barMap_app`, the module-hom `f` projections, the pairing lemmas), so
  -- `rfl`/`exact` cross the `barObj`/`barData.obj` gap that blocks `rw`/`simp`
  -- motives (which re-check at implicit transparency).
  have p1 : (monadPow T.adj.toMonad 0).map φ.f = φ.f := by
    change (𝟭 C).map φ.f = φ.f
    exact Functor.id_map _
  have qA' : (adjAlg alg').a = alg'.a :=
    Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
  have qA : (adjAlg alg).a = alg.a :=
    Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
  have eL : (barMap (𝟙 ((adjRightModule T.adj).postcomp T.forget))
        (algebraLeftModuleHom ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) 0 ≫
        (adjUnderlyingPairing alg').pairing).app X
      = ((((adjRightModule T.adj).postcomp T.forget).functor.map
        ((monadPow T.adj.toMonad 0).map φ.f) ≫ 𝟙 _) ≫ (adjAlg alg').a) := rfl
  have eR : (adjUnderlyingPairing alg).pairing.app X ≫
      (adjUnderlyingTargetHom φ).app X = alg.a ≫ φ.f :=
    congrArg (· ≫ φ.f) qA
  have q1 : (((adjRightModule T.adj).postcomp T.forget).functor.map
      ((monadPow T.adj.toMonad 0).map φ.f))
      = (((adjRightModule T.adj).postcomp T.forget).functor.map φ.f) :=
    congrArg _ p1
  have q2 : ((((adjRightModule T.adj).postcomp T.forget).functor.map
      ((monadPow T.adj.toMonad 0).map φ.f) ≫ 𝟙 _))
      = (((adjRightModule T.adj).postcomp T.forget).functor.map φ.f) :=
    (Category.comp_id _).trans q1
  have eM : ((((adjRightModule T.adj).postcomp T.forget).functor.map
      ((monadPow T.adj.toMonad 0).map φ.f) ≫ 𝟙 _) ≫ (adjAlg alg').a)
      = ((((adjRightModule T.adj).postcomp T.forget).functor.map φ.f) ≫ alg'.a) :=
    (congrArg (· ≫ (adjAlg alg').a) q2).trans
      (congrArg ((((adjRightModule T.adj).postcomp T.forget).functor.map φ.f) ≫ ·) qA')
  have hRT : (((adjRightModule T.adj).postcomp T.forget).functor.map φ.f)
      = T.map φ.f := rfl
  have eN : ((((adjRightModule T.adj).postcomp T.forget).functor.map φ.f) ≫ alg'.a)
      = alg.a ≫ φ.f :=
    (congrArg (· ≫ alg'.a) hRT).trans φ.h
  exact eL.trans (eM.trans (eN.trans eR.symm))

/-- For a monad T on C and an algebra morphism φ : alg → alg′, the pairing-preserving bar map with
identity right-module component and restricted algebra left-module component gives
adjEvaluatedAugmented(alg) → adjEvaluatedAugmented(alg′). It is obtained by evaluating the
corresponding augmented two-sided bar map at the unique discrete point. -/
@[no_expose]
noncomputable def adjEvaluatedHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    adjEvaluatedAugmented alg ⟶ adjEvaluatedAugmented alg' :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).map
    (BalancedPairing.toSimplicialAugmentedMap (adjUnderlyingPairing alg)
      (adjUnderlyingPairing alg')
      (𝟙 ((adjRightModule T.adj).postcomp T.forget))
      (algebraLeftModuleHom ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
      (adjUnderlyingTargetHom φ)
      (adjUnderlying_hq φ))

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The simplicial component of
adjEvaluatedHom(φ) is the augmented balanced-pairing map, with identity forgotten right-module
map and restricted algebra left-module map, followed by evaluation at the unique point. This
specifies its action on every bar degree. -/
private theorem adjEvaluatedHom_left {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (adjEvaluatedHom φ).left =
      Functor.whiskerRight
        (BalancedPairing.toSimplicialAugmentedMap (adjUnderlyingPairing alg)
          (adjUnderlyingPairing alg')
          (𝟙 ((adjRightModule T.adj).postcomp T.forget))
          (algebraLeftModuleHom
            ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
          (adjUnderlyingTargetHom φ)
          (adjUnderlying_hq φ)).left resolutionEvalPoint := rfl

/-- For a monad T on C and algebra morphism φ : alg → alg′, the target component of
adjEvaluatedHom(φ) equals evaluation of adjUnderlyingTargetHom(φ) at the unique discrete
point. It therefore represents φ.f after the augmentation-target identifications. -/
private theorem adjEvaluatedHom_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (adjEvaluatedHom φ).right =
      resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) := rfl

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The canonical comparison γ from
the evaluated adjunction bar to the underlying Eilenberg–Moore bar satisfies γ_alg ≫
emUnderlyingHom(φ) = adjEvaluatedHom(φ) ≫ γ_alg′. This is an equality of augmented simplicial
maps, including the augmentation-target components. -/
theorem adjToEMComparison_naturality {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    adjToEMComparison alg ≫ emUnderlyingHom φ =
      adjEvaluatedHom φ ≫ adjToEMComparison alg' := by
  apply SimplicialObject.Augmented.hom_ext
  · -- `_`-threaded term mode: every `rw` motive stays over folded or
    -- genuine-simplicial terms. Unfolding `adjToEMComparison_left`-style
    -- equations inside one big `rw` left the goal ill-typed at implicit
    -- transparency (the `toSimplicialFunctor` gap) and later `rw`s failed.
    have e12 : ((adjToEMComparison alg ≫ emUnderlyingHom φ).left) =
        (Functor.whiskerRight
          ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg)).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg))
          resolutionEvalPoint ≫
        algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) φ) := by
      rw [Comma.comp_left, adjToEMComparison_left, emUnderlyingHom_left]
      -- `rw` normalizes the LHS to the stated RHS but its auto-`rfl`
      -- (reducible transparency) does not close across the
      -- `toSimplicialFunctor` gap; explicit `rfl` (default) does.
      rfl
    have eC : ((adjUnderlyingPairing alg).toSimplicialAugmentedMap
          (adjUnderlyingPairing alg') (𝟙 ((adjRightModule T.adj).postcomp T.forget))
          (algebraLeftModuleHom
            ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
          (adjUnderlyingTargetHom φ) (adjUnderlying_hq φ)).left =
        twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
          (algebraLeftModuleHom
            ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) :=
      BalancedPairing.toSimplicialAugmentedMap_left _ _ _ _ _ _
    have e45 : ((adjEvaluatedHom φ ≫ adjToEMComparison alg').left) =
        (Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)))
          resolutionEvalPoint ≫
        Functor.whiskerRight
          ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg')).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg'))
          resolutionEvalPoint) := by
      rw [Comma.comp_left, adjEvaluatedHom_left, adjToEMComparison_left, eC]
      -- `rw` normalizes the LHS to the stated RHS but its auto-`rfl`
      -- (reducible transparency) does not close across the
      -- `toSimplicialFunctor` gap; explicit `rfl` (default) does.
      rfl
    have heL : (adjLeftIso (T := T) alg).hom ≫
          (leftModuleRestrictAlongHom (adjMonadHom (T := T))).map
            (algebraLeftModuleHom φ) =
        algebraLeftModuleHom
            ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ) ≫
          (adjLeftIso (T := T) alg').hom := by
      refine Algebra.Hom.ext' _ _ _ _ ?_
      ext X0
      simp only [Algebra.comp_f, adjLeftIso_hom_f]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    have hslide := (barChangeHom_naturality (adjMonadHom (T := T))
      (𝟙 (emRightModule.postcomp T.forget)) (algebraLeftModuleHom φ)).symm
    have hW : (Functor.whiskerRight
          ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg)).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg))
          resolutionEvalPoint ≫
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 (emRightModule.postcomp T.forget))
            (algebraLeftModuleHom φ))
          ((evaluation (Discrete PUnit.{1}) C).obj
            (⟨PUnit.unit⟩ : Discrete PUnit.{1}))) =
        (Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)))
          resolutionEvalPoint ≫
        Functor.whiskerRight
          ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg')).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg'))
          resolutionEvalPoint) := by
      -- `hEVAL'` aligns the evaluation object to `resolutionEvalPoint` by
      -- `rfl` on a *single-factor* equation (motive-local, well-typed);
      -- `rw [hEVAL']` then abstracts only that hom (pinned type, safe),
      -- unlike `rw [hEVAL]` which abstracts the shared object into a
      -- motive over the still-concrete first factor (ill-typed at implicit
      -- transparency). The rest are hom-pattern rewrites (safe motives).
      have hEVAL' : Functor.whiskerRight
            (twoSidedBarHom (𝟙 (emRightModule.postcomp T.forget))
              (algebraLeftModuleHom φ))
            ((evaluation (Discrete PUnit.{1}) C).obj
              (⟨PUnit.unit⟩ : Discrete PUnit.{1})) =
          Functor.whiskerRight
            (twoSidedBarHom (𝟙 (emRightModule.postcomp T.forget))
              (algebraLeftModuleHom φ))
            resolutionEvalPoint := rfl
      rw [hEVAL']
      -- Whiskered same-functor pairs combine in term mode
      -- (`Eq.trans`/`congrArg`, default transparency). `rw` cannot form the
      -- motive here: the goal is ill-typed at implicit transparency (the
      -- `toSimplicialFunctor` gap), so even `rw` matching fails with
      -- "did not find occurrence". The middle-composite rewrite stays in
      -- hom-pattern `rw` (safe motives) on the unwhiskered equality.
      have mid : ((((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg)).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg)) ≫
          twoSidedBarHom (𝟙 (emRightModule.postcomp T.forget))
            (algebraLeftModuleHom φ))) =
          (((twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))) ≫
          ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg')).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg')))) := by
        -- Safe prefix: unfold Isos (rfl), reassoc, slide, simplify
        -- right-module map, reassoc, fuse LHS pair, simplify right identity.
        -- All motives are hom-pattern and well-typed at implicit transparency.
        rw [twoSidedBarIso_hom, twoSidedBarIso_hom, Category.assoc, hslide,
          Functor.map_id, ← Category.assoc, twoSidedBarHom_comp,
          Category.comp_id]
        -- Align LHS left-module composite via `heL` (module-hom motive, safe).
        rw [heL]
        -- Remaining goal fuses the RHS pair `D ≫ I`, whose middle object is
        -- only semireducibly equal (`adjAlg` vs `obj` unfolding), so `rw`
        -- cannot form the motive at implicit transparency. Finish in term
        -- mode (default transparency) with explicit typed equalities.
        have hDI : (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) ≫
            twoSidedBarHom adjRightIso.hom (adjLeftIso alg').hom) =
            twoSidedBarHom adjRightIso.hom
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ) ≫
              (adjLeftIso alg').hom) := by
          have hcomp := twoSidedBarHom_comp
            (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            adjRightIso.hom
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
            (adjLeftIso alg').hom
          have hid : (𝟙 ((adjRightModule T.adj).postcomp T.forget) ≫
              adjRightIso.hom) = adjRightIso.hom :=
            Category.id_comp _
          exact hcomp.trans (congrArg
            (fun gR => twoSidedBarHom gR
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ) ≫
              (adjLeftIso alg').hom)) hid)
        have hRHS : (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) ≫
            (twoSidedBarHom adjRightIso.hom (adjLeftIso alg').hom ≫
              barChangeHom (adjMonadHom (T := T))
                (emRightModule.postcomp T.forget) (algebraLeftModule alg'))) =
            ((twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) ≫
            twoSidedBarHom adjRightIso.hom (adjLeftIso alg').hom) ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg')) :=
          (Category.assoc _ _ _).symm
        exact (hRHS.trans (congrArg
          (fun x => x ≫ barChangeHom (adjMonadHom (T := T))
            (emRightModule.postcomp T.forget) (algebraLeftModule alg')) hDI)).symm
      exact (Functor.whiskerRight_comp _ _ _).symm.trans
        ((congrArg (fun f => Functor.whiskerRight f resolutionEvalPoint) mid).trans
          (Functor.whiskerRight_comp _ _ _))
    exact e12.trans (hW.trans e45.symm)
  · have eR12 : ((adjToEMComparison alg ≫ emUnderlyingHom φ).right) =
        (resolutionEvalPoint.map (adjDataAugHom alg).right ≫ φ.f) := by
      rw [Comma.comp_right, adjToEMComparison_right, emUnderlyingHom_right]
      rfl
    have eR45 : ((adjEvaluatedHom φ ≫ adjToEMComparison alg').right) =
        (resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) ≫
          resolutionEvalPoint.map (adjDataAugHom alg').right) := by
      rw [Comma.comp_right, adjEvaluatedHom_right, adjToEMComparison_right]
      rfl
    -- Concrete-level closure: both whiskered Data-identities are identities
    -- (the `𝟙 _` objects come from `Functor.map_id`, never inferred against
    -- hidden types), and the whiskered target map is `φ.f` (evaluation acts
    -- by application). All unfolding below stays over private/public
    -- helpers, never over hidden `.right`s.
    have hL := (congrArg resolutionEvalPoint.map
      (rfl : (adjDataAugHom (T := T) alg).right = 𝟙 _)).trans
      (Functor.map_id _ _)
    have hR := (congrArg resolutionEvalPoint.map
      (rfl : (adjDataAugHom (T := T) alg').right = 𝟙 _)).trans
      (Functor.map_id _ _)
    have uEq : resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) =
        φ.f :=
      (adjEvalPoint_map_app _).trans (adjUnderlyingTargetHom_app _ _)
    -- Term-mode closure: `rw` would rebuild motives at implicit
    -- transparency, where the inferred `𝟙 _` objects (spelled through
    -- `.toAugmented.right`) do not re-unfold. `congrArg`/`trans` elaborate
    -- at default transparency and avoid motives entirely.
    have h2map : (resolutionEvalPoint.map (adjDataAugHom alg).right ≫ φ.f) =
        (resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) ≫
          resolutionEvalPoint.map (adjDataAugHom alg').right) :=
      let step1 : (resolutionEvalPoint.map (adjDataAugHom alg).right ≫ φ.f) =
          φ.f :=
        (congrArg (· ≫ φ.f) hL).trans (Category.id_comp _)
      let step2 : (resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) ≫
          resolutionEvalPoint.map (adjDataAugHom alg').right) =
          resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) :=
        (congrArg
          (resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) ≫ ·)
          hR).trans (Category.comp_id _)
      step1.trans (step2.trans uEq).symm
    exact eR12.trans (h2map.trans eR45.symm)

/-- For a monad T on C and an algebra morphism φ : alg → alg′, let e_alg and e_alg′ identify the
augmentation targets of the evaluated adjunction bars with their algebra carriers. Then
adjEvaluatedHom(φ).right ≫ eqToHom(e_alg′) = eqToHom(e_alg) ≫ φ.f. The equation fixes the
source and target transports of the carrier map. -/
theorem adjEvaluatedHom_right_eqToHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (adjEvaluatedHom φ).right ≫ eqToHom (adjEvaluatedAugmented_point alg') =
      eqToHom (adjEvaluatedAugmented_point alg) ≫ φ.f := by
  have hR : (adjEvaluatedHom (T := T) φ).right =
      resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) :=
    adjEvaluatedHom_right φ
  have uEq : resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) =
      φ.f :=
    (adjEvalPoint_map_app _).trans (adjUnderlyingTargetHom_app _ _)
  have hRightEq : (adjEvaluatedHom (T := T) φ).right = φ.f :=
    hR.trans uEq
  have hStep1 : ((adjEvaluatedHom (T := T) φ).right ≫
      eqToHom (adjEvaluatedAugmented_point alg')) =
      (φ.f ≫ eqToHom (adjEvaluatedAugmented_point alg')) :=
    congrArg (· ≫ eqToHom (adjEvaluatedAugmented_point alg')) hRightEq
  have hStep2 : (φ.f ≫ eqToHom (adjEvaluatedAugmented_point alg')) =
      (eqToHom (adjEvaluatedAugmented_point alg) ≫ φ.f) := by
    have hL : (φ.f ≫ eqToHom (adjEvaluatedAugmented_point alg')) = φ.f :=
      Category.comp_id _ |>.trans (by rfl)
    have hRr : (eqToHom (adjEvaluatedAugmented_point alg) ≫ φ.f) = φ.f :=
      Category.id_comp _ |>.trans (by rfl)
    exact hL.trans hRr.symm
  exact hStep1.trans hStep2

/-- Let T be a monad on C and alg a T-algebra. The evaluated restricted-adjunction bar map induced
by 𝟙_alg equals the identity of adjEvaluatedAugmented(alg), on both its simplicial object and
its augmentation target. -/
theorem adjEvaluatedHom_id (alg : T.Algebra) :
    adjEvaluatedHom (𝟙 alg) = 𝟙 (adjEvaluatedAugmented alg) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have e1 : (adjEvaluatedHom (𝟙 alg)).left =
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map (𝟙 alg))))
          resolutionEvalPoint := by
      simp only [adjEvaluatedHom,
        SimplicialObject.Augmented.whiskeringObj_map_left]
      rfl
    have eMapId : ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map
        (𝟙 alg)) = 𝟙 _ := by
      rw [Functor.map_id]
    have eLeftHom : (algebraLeftModuleHom
        ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map (𝟙 alg))) =
        𝟙 _ := by
      rw [eMapId]
      exact algebraLeftModuleHom_id _
    have e2 : Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map (𝟙 alg))))
          resolutionEvalPoint =
        𝟙 ((adjEvaluatedAugmented alg).left) := by
      rw [eLeftHom, twoSidedBarHom_id, Functor.whiskerRight_id']
      rfl
    exact e1.trans e2
  · have e1r : (adjEvaluatedHom (𝟙 alg)).right =
        resolutionEvalPoint.map (adjUnderlyingTargetHom (𝟙 alg)) := by
      rw [adjEvaluatedHom_right]
    have eTargetId : (adjUnderlyingTargetHom (𝟙 alg)) = 𝟙 _ := by
      ext X
      simp only [adjUnderlyingTargetHom_app, Algebra.id_f, NatTrans.id_app]
      rfl
    have e2r : resolutionEvalPoint.map (adjUnderlyingTargetHom (𝟙 alg)) =
        𝟙 (adjEvaluatedAugmented alg).right := by
      rw [eTargetId]
      exact Functor.map_id _ _
    exact e1r.trans e2r

/-- For a monad T on C and algebra morphisms φ : alg₁ → alg₂, ψ : alg₂ → alg₃, adjEvaluatedHom(φ)
≫ adjEvaluatedHom(ψ) = adjEvaluatedHom(φ ≫ ψ). The equality is of augmented simplicial maps of
C. -/
theorem adjEvaluatedHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    adjEvaluatedHom φ ≫ adjEvaluatedHom ψ = adjEvaluatedHom (φ ≫ ψ) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have f1 : (adjEvaluatedHom φ ≫ adjEvaluatedHom ψ).left =
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)))
          resolutionEvalPoint ≫
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map ψ)))
          resolutionEvalPoint := by
      rw [Comma.comp_left]
      simp only [adjEvaluatedHom,
        SimplicialObject.Augmented.whiskeringObj_map_left]
      rfl
    have fMap : ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map
        (φ ≫ ψ)) =
        ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ) ≫
        ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map ψ) := by
      rw [Functor.map_comp]
    have f2 : Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)))
          resolutionEvalPoint ≫
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map ψ)))
          resolutionEvalPoint =
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map (φ ≫ ψ))))
          resolutionEvalPoint := by
      rw [← Functor.whiskerRight_comp, twoSidedBarHom_comp, Category.id_comp,
        algebraLeftModuleHom_comp, ← fMap]
    have f3 : Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map (φ ≫ ψ))))
          resolutionEvalPoint =
        (adjEvaluatedHom (φ ≫ ψ)).left :=
      rfl
    exact f1.trans (f2.trans f3)
  · have g1 : (adjEvaluatedHom φ ≫ adjEvaluatedHom ψ).right =
        resolutionEvalPoint.map (adjUnderlyingTargetHom φ) ≫
          resolutionEvalPoint.map (adjUnderlyingTargetHom ψ) :=
      rfl
    have gTarget : (adjUnderlyingTargetHom (φ ≫ ψ)) =
        (adjUnderlyingTargetHom φ) ≫ (adjUnderlyingTargetHom ψ) := by
      ext X
      simp only [adjUnderlyingTargetHom_app, Algebra.comp_f,
        NatTrans.comp_app]
      rfl
    have g2 : resolutionEvalPoint.map (adjUnderlyingTargetHom φ) ≫
        resolutionEvalPoint.map (adjUnderlyingTargetHom ψ) =
        resolutionEvalPoint.map (adjUnderlyingTargetHom (φ ≫ ψ)) := by
      rw [← Functor.map_comp, ← gTarget]
    have g3 : resolutionEvalPoint.map (adjUnderlyingTargetHom (φ ≫ ψ)) =
        (adjEvaluatedHom (φ ≫ ψ)).right := by
      rw [adjEvaluatedHom_right]
    exact g1.trans (g2.trans g3)

/-- For a monad T on C and a T-algebra alg, the simplicial projection of the forward augmented
isomorphism adjLiteralIso(alg) equals the forward map of adjLiteralBarIso(alg). Thus its left
component is the already specified comparison of the two simplicial bar descriptions. -/
private theorem adjLiteralIso_hom_left_aux (alg : T.Algebra) :
    ((adjLiteralIso alg).hom).left = (adjLiteralBarIso alg).hom :=
  rfl

/-- Let T be a monad on C and alg a T-algebra. The forward morphism of adjLiteralIso(alg) has
underlying simplicial map adjLiteralBarIso(alg).hom, from the evaluated-and-forgotten bar to
the restricted-module bar description. -/
theorem adjLiteralIso_hom_left (alg : T.Algebra) :
    ((adjLiteralIso alg).hom).left = (adjLiteralBarIso alg).hom :=
  adjLiteralIso_hom_left_aux alg

/-- For a monad T on C and a T-algebra alg, the target projection of adjLiteralIso(alg).hom is the
identity of the augmentation target of adjLiteralAugmented(alg). This is the
carrier-preserving right component of the augmented isomorphism. -/
private theorem adjLiteralIso_hom_right_aux (alg : T.Algebra) :
    ((adjLiteralIso alg).hom).right =
      𝟙 (adjLiteralAugmented alg).right :=
  rfl

/-- Let T be a monad on C and alg a T-algebra. If e_lit and e_eval identify the augmentation
targets of adjLiteralAugmented(alg) and adjEvaluatedAugmented(alg) with alg.A, then
adjLiteralIso(alg).hom.right ≫ eqToHom(e_eval) = eqToHom(e_lit). The target component is
therefore the identity after the specified object identifications. -/
theorem adjLiteralIso_hom_right_eqToHom (alg : T.Algebra) :
    ((adjLiteralIso alg).hom).right ≫
      eqToHom (adjEvaluatedAugmented_point alg) =
      eqToHom (adjLiteralAugmented_point alg) := by
  have hR : ((adjLiteralIso (T := T) alg).hom).right =
      𝟙 (adjLiteralAugmented (T := T) alg).right :=
    adjLiteralIso_hom_right_aux alg
  have hStep1 : (((adjLiteralIso (T := T) alg).hom).right ≫
      eqToHom (adjEvaluatedAugmented_point alg)) =
      (𝟙 _ ≫ eqToHom (adjEvaluatedAugmented_point alg)) :=
    congrArg (· ≫ eqToHom (adjEvaluatedAugmented_point alg)) hR
  have hStep2 : (𝟙 (adjLiteralAugmented (T := T) alg).right ≫
      eqToHom (adjEvaluatedAugmented_point alg)) =
      eqToHom (adjLiteralAugmented_point alg) := by
    have hL : (𝟙 (adjLiteralAugmented (T := T) alg).right ≫
        eqToHom (adjEvaluatedAugmented_point alg)) =
        eqToHom (adjEvaluatedAugmented_point alg) :=
      Category.id_comp _ |>.trans (by rfl)
    have hRr : (eqToHom (adjLiteralAugmented_point alg)) =
        eqToHom (adjEvaluatedAugmented_point alg) := by rfl
    exact hL.trans hRr.symm
  exact hStep1.trans hStep2

/-- For a monad T on C and a T-algebra alg, compose adjLiteralIso(alg).hom with
adjToEMComparison(alg) to define an augmented map adjLiteralAugmented(alg) →
emUnderlyingAugmented(alg). This compares the evaluated-and-forgotten adjunction bar with the
underlying Eilenberg–Moore bar through its restricted-module description. -/
noncomputable def adjLiteralToEMComparison (alg : T.Algebra) :
    adjLiteralAugmented alg ⟶ emUnderlyingAugmented alg :=
  (adjLiteralIso alg).hom ≫ adjToEMComparison alg

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The augmented comparison
e=adjLiteralIso satisfies adjLiteralHom(φ) ≫ e_alg′.hom = e_alg.hom ≫ adjEvaluatedHom(φ). Thus
the comparison respects the maps induced by every algebra morphism. -/
theorem adjLiteralIso_naturality {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    adjLiteralHom φ ≫ (adjLiteralIso alg').hom =
      (adjLiteralIso alg).hom ≫ adjEvaluatedHom φ := by
  apply SimplicialObject.Augmented.hom_ext
  · have eL12 : ((adjLiteralHom φ ≫ (adjLiteralIso alg').hom).left) =
        (adjLiteralHom φ).left ≫ (adjLiteralBarIso alg').hom := by
      rw [Comma.comp_left, adjLiteralIso_hom_left]
    have eL45 : (((adjLiteralIso alg).hom ≫ adjEvaluatedHom φ).left) =
        (adjLiteralBarIso alg).hom ≫ (adjEvaluatedHom φ).left := by
      rw [Comma.comp_left, adjLiteralIso_hom_left]
    have hEvalL : (adjEvaluatedHom (T := T) φ).left =
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)))
          resolutionEvalPoint := by
      have hC : ((adjUnderlyingPairing alg).toSimplicialAugmentedMap
            (adjUnderlyingPairing alg') (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
            (adjUnderlyingTargetHom φ) (adjUnderlying_hq φ)).left =
          twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) :=
        BalancedPairing.toSimplicialAugmentedMap_left _ _ _ _ _ _
      have hW : (adjEvaluatedHom (T := T) φ).left =
          Functor.whiskerRight
            ((adjUnderlyingPairing alg).toSimplicialAugmentedMap
              (adjUnderlyingPairing alg') (𝟙 ((adjRightModule T.adj).postcomp T.forget))
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
              (adjUnderlyingTargetHom φ) (adjUnderlying_hq φ)).left
            resolutionEvalPoint := rfl
      exact hW.trans
        (congrArg (fun m => Functor.whiskerRight m resolutionEvalPoint) hC)
    ext Δ
    have hIso : ((adjLiteralBarIso (T := T) alg).hom).app Δ =
        eqToHom (adjLiteralBar_obj_eq alg Δ) := by
      have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
        obtain ⟨d⟩ := Δ
        exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
      rw [hΔ]
      exact adjLiteralBarIso_hom_app alg _
    have hIso' : ((adjLiteralBarIso (T := T) alg').hom).app Δ =
        eqToHom (adjLiteralBar_obj_eq alg' Δ) := by
      have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
        obtain ⟨d⟩ := Δ
        exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
      rw [hΔ]
      exact adjLiteralBarIso_hom_app alg' _
    have hLit : ((adjLiteralHom (T := T) φ).left).app Δ =
        T.forget.map ((((adjAugmented T.adj).left).obj Δ).map φ) :=
      adjLiteralHom_left_app _ _
    have hEval : ((adjEvaluatedHom (T := T) φ).left).app Δ =
        resolutionEvalPoint.map
          ((twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))).app
            Δ) := by
      rw [hEvalL]
      rfl
    rw [eL12, eL45] at *
    simp only [NatTrans.comp_app] at *
    rw [hLit, hEval, hIso, hIso']
    have hAgree : T.forget.map ((((adjAugmented T.adj).left).obj Δ).map φ) ≫
        eqToHom (adjLiteralBar_obj_eq alg' Δ) =
        eqToHom (adjLiteralBar_obj_eq alg Δ) ≫
          resolutionEvalPoint.map
            ((twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))).app
              Δ) := by
      have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
        obtain ⟨d⟩ := Δ
        exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
      rw [hΔ]
      have hIdL : eqToHom (adjLiteralBar_obj_eq alg
          (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) =
          𝟙 _ := rfl
      have hIdR : eqToHom (adjLiteralBar_obj_eq alg'
          (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) =
          𝟙 _ := rfl
      erw [hIdL, hIdR, Category.comp_id, Category.id_comp]
      -- Both sides compute to forgotten free-monad-pow maps over the same
      -- monad `T.adj.toMonad`: unfold via the `rfl` computation lemmas.
      have hψ : (((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ).f) =
          φ.f := rfl
      -- Bind the identity module hom so `.f` resolves (dot notation does
      -- not unfold `𝟙`-headed applications); the factor is then `rfl`.
      set fR1 : (adjRightModule T.adj).postcomp T.forget ⟶
          (adjRightModule T.adj).postcomp T.forget := 𝟙 _ with hdef
      have h1R : ∀ (X : C), (fR1.f.app X) = 𝟙 _ := fun X => rfl
      simp only [adjAugmented_left, adjBar_obj_map, adjRightModule_functor,
        adjEvalPoint_map_app,
        twoSidedBarHom_app_app_op_mk, algebraLeftModuleHom_f_app,
        Monad.forget_map, hψ, h1R, RightModule.postcomp_functor,
        Functor.comp_map]
      -- Residue: forgotten map vs its `.f` form plus `≫ 𝟙`; close in
      -- term mode (no `rw` motives over the forgotten types).
      have eF : T.forget.map (T.free.map ((T.adj.toMonad.monadPow
          (Opposite.unop Δ).len).map φ.f)) =
          (T.free.map ((T.adj.toMonad.monadPow
            (Opposite.unop Δ).len).map φ.f)).f :=
        Monad.forget_map _ _
      exact eF.trans (Category.comp_id _).symm
    exact hAgree
  · have eR12 : ((adjLiteralHom φ ≫ (adjLiteralIso alg').hom).right) =
        (φ.f ≫ ((adjLiteralIso alg').hom).right) :=
      Comma.comp_right.trans
        (congrArg (· ≫ ((adjLiteralIso alg').hom).right)
          (adjLiteralHom_right φ))
    have eR45 : (((adjLiteralIso alg).hom ≫ adjEvaluatedHom φ).right) =
        (((adjLiteralIso alg).hom).right ≫
          resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ)) :=
      Comma.comp_right.trans
        (congrArg (((adjLiteralIso alg).hom).right ≫ ·)
          (adjEvaluatedHom_right φ))
    have hIsoR : ((adjLiteralIso (T := T) alg).hom).right =
        𝟙 (adjLiteralAugmented (T := T) alg).right :=
      adjLiteralIso_hom_right_aux alg
    have hIsoR' : ((adjLiteralIso (T := T) alg').hom).right =
        𝟙 (adjLiteralAugmented (T := T) alg').right :=
      adjLiteralIso_hom_right_aux alg'
    have uEq : resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) =
        φ.f :=
      (adjEvalPoint_map_app _).trans (adjUnderlyingTargetHom_app _ _)
    have hLhs : (φ.f ≫ ((adjLiteralIso alg').hom).right) = φ.f := by
      rw [hIsoR']
      exact Category.comp_id _
    have hRhs : (((adjLiteralIso alg).hom).right ≫
        resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ)) = φ.f := by
      rw [hIsoR, uEq]
      exact Category.id_comp _
    exact eR12.trans (hLhs.trans (hRhs.symm.trans eR45.symm))

/-- For a monad T on C and an algebra morphism φ : alg → alg′, let δ be adjLiteralToEMComparison.
Then adjLiteralHom(φ) ≫ δ_alg′ = δ_alg ≫ emUnderlyingHom(φ). This is the naturality equation
of the augmented map from the evaluated-and-forgotten adjunction bar to the underlying
Eilenberg–Moore bar. -/
theorem adjLiteralToEMComparison_naturality {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') :
    adjLiteralHom φ ≫ adjLiteralToEMComparison alg' =
      adjLiteralToEMComparison alg ≫ emUnderlyingHom φ := by
  have h1 := adjLiteralIso_naturality (T := T) φ
  have h2 := adjToEMComparison_naturality (T := T) φ
  change adjLiteralHom φ ≫
      ((adjLiteralIso alg').hom ≫ adjToEMComparison alg') =
    ((adjLiteralIso alg).hom ≫ adjToEMComparison alg) ≫ emUnderlyingHom φ
  calc adjLiteralHom φ ≫ ((adjLiteralIso alg').hom ≫ adjToEMComparison alg')
      _ = (adjLiteralHom φ ≫ (adjLiteralIso alg').hom) ≫
          adjToEMComparison alg' :=
        (Category.assoc _ _ _).symm
      _ = ((adjLiteralIso alg).hom ≫ adjEvaluatedHom φ) ≫
          adjToEMComparison alg' :=
        congrArg (· ≫ adjToEMComparison alg') h1
      _ = (adjLiteralIso alg).hom ≫
          (adjEvaluatedHom φ ≫ adjToEMComparison alg') :=
        Category.assoc _ _ _
      _ = (adjLiteralIso alg).hom ≫
          (adjToEMComparison alg ≫ emUnderlyingHom φ) :=
        congrArg ((adjLiteralIso alg).hom ≫ ·) h2.symm
      _ = ((adjLiteralIso alg).hom ≫ adjToEMComparison alg) ≫
          emUnderlyingHom φ :=
        (Category.assoc _ _ _).symm

end AdjEMComparison

end Monad
end CategoryTheory
