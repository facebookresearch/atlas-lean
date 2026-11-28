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

public import MathlibExt.CategoryTheory.Monad.BarResolution

/-!
# The free-algebra bar of a monad and its underlying simplicial object

Let T be a monad on a category C and alg=(A,a) a T-algebra. The free-algebra functor is a
right T-module with action induced by monad multiplication. Together with the constant left
module of alg, it gives an Eilenberg–Moore-valued two-sided bar whose degree-n term is the
free algebra on T^n(A). The action a gives an augmentation to alg.

Algebra morphisms induce augmented bar maps. Evaluating at the unique discrete point and
forgetting the algebra structure gives an augmented simplicial object of C, canonically
isomorphic to the regular-right monadic bar B(T,T,A). The comparison respects algebra
morphisms and transports the outer-unit extra degeneracy of that underlying bar.

The two-sided bar convention follows J. P. May, *The Geometry of Iterated Loop Spaces*,
Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9, Construction 9.6 and Remark 9.12,
<https://doi.org/10.1007/BFb0067491>. No additive or monadicity hypothesis on C is required.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {T : Monad C}

section EMModule

/-- Let T be a monad on C. There is a natural transformation T ⋙ T.free → T.free whose component
at X is the algebra morphism from the free algebra on T(X) to the free algebra on X with
underlying map μ_X : T²(X) → T(X). Monad associativity makes this an algebra morphism. -/
def emAction : T.toFunctor ⋙ Monad.free T ⟶ Monad.free T where
  app X :=
    { f := T.μ.app X
      h := T.assoc X }
  naturality X Y f := by
    ext
    exact T.μ.naturality f

/-- For a monad T on C and X ∈ C, the underlying morphism of emAction_X : free(TX) → free(X) is
μ_X. Thus the natural free-algebra action has monad multiplication as its map in C. -/
@[simp]
theorem emAction_f (X : C) : (emAction.app X).f = T.μ.app X :=
  rfl

/-- Let T be a monad on C. The functor T.free : C → T.Algebra is a right T-module with action
free(TX) → free(X) induced by μ_X. Its module unit and associativity laws are the
corresponding monad laws. This right module takes values in the Eilenberg–Moore category. -/
def emRightModule : RightModule T T.Algebra :=
  RightModule.mk (Monad.free T) emAction (fun X => by ext; exact T.right_unit X)
    (fun X => by ext; exact T.assoc X)

/-- For a monad T on C, the underlying functor of emRightModule is T.free : C → T.Algebra. It
sends X to the algebra (T(X),μ_X). -/
@[simp]
theorem emRightModule_functor : emRightModule.functor = Monad.free T :=
  rfl

/-- Let T be a monad on C and X ∈ C. The action component of emRightModule at X equals emAction_X,
the algebra morphism free(TX) → free(X) induced by μ_X. -/
@[simp]
theorem emRightModule_action_app (X : C) :
    (emRightModule (T := T)).action.app X = emAction.app X :=
  rfl

/-- For a monad T on C and X ∈ C, the underlying C-morphism of the free-algebra right-module
action at X is μ_X : T²(X) → T(X). This identifies the action after forgetting its algebra
structure. -/
@[simp]
theorem emRightModule_action_f (X : C) :
    (emRightModule.action.app X).f = T.μ.app X :=
  rfl

/-- Let T be a monad on C and g : X → Y. The underlying map of emRightModule.functor(g), the
free-algebra morphism free(X) → free(Y), equals T(g) : T(X) → T(Y). -/
@[simp]
theorem emRightModule_functor_map_f {X Y : C} (g : X ⟶ Y) :
    (emRightModule.functor.map g).f = T.map g :=
  rfl

/-- For a monad T on C and g : X → Y, postcomposing the free-algebra right module with T.forget
gives the map T(g). Its underlying endofunctor of C is T. -/
@[simp]
theorem emPostcomp_functor_map {X Y : C} (g : X ⟶ Y) :
    (emRightModule.postcomp T.forget).functor.map g = T.map g :=
  rfl

/-- Let T be a monad on C and X ∈ C. The action at X of emRightModule postcomposed with T.forget
is exactly μ_X : T²(X) → T(X). -/
@[simp]
theorem emPostcomp_action_app (X : C) :
    (emRightModule.postcomp T.forget).action.app X = T.μ.app X :=
  rfl

/-- For a monad T on C, the free-algebra right module postcomposed with T.forget is isomorphic to
the regular right T-module. Both have underlying functor T and action μ, and the chosen module
isomorphism is the identity on their carrier functor. -/
noncomputable def emModuleIso :
    emRightModule.postcomp T.forget ≅ RightModule.regular T :=
  Iso.refl _

/-- For a monad T on C and X ∈ C, the underlying component at X of emModuleIso.hom is 𝟙_{T(X)}.
This is the forward comparison from the forgotten free right module to the regular right
module. -/
@[simp]
theorem emModuleIso_hom_f_app (X : C) :
    ((emModuleIso (T := T)).hom.f).app X = 𝟙 _ :=
  rfl

/-- Let T be a monad on C and X ∈ C. The underlying component at X of emModuleIso.inv is 𝟙_{T(X)},
returning the regular right module to the forgotten free-algebra right module. -/
@[simp]
theorem emModuleIso_inv_f_app (X : C) :
    ((emModuleIso (T := T)).inv.f).app X = 𝟙 _ :=
  rfl

end EMModule

section EMBar

/-- Let T be a monad on C and alg=(A,a) a T-algebra. The two-sided bar of the free-algebra right
T-module and the constant left T-module of alg is a simplicial object in Discrete PUnit ⥤
T.Algebra. In degree n its value at the unique point is free(T^n(A)), with carrier T(T^n(A))
and structure map μ_{T^n(A)}. -/
noncomputable def emBar (alg : T.Algebra) :
    SimplicialObject (Discrete PUnit.{1} ⥤ T.Algebra) :=
  twoSidedBar T emRightModule (algebraLeftModule alg)

/-- For a monad T on C, T-algebra alg, and n ∈ ℕ, emBar(alg) at the opposite simplex [n] equals
B(emRightModule,T,algebraLeftModule(alg))_n. This is the constant-index functor with value the
free algebra on T^n(alg.A). -/
@[simp]
theorem emBar_obj (alg : T.Algebra) (n : ℕ) :
    (emBar alg).obj (Opposite.op (SimplexCategory.mk n)) =
      barObj T emRightModule (algebraLeftModule alg) n :=
  rfl

/-- Let T be a monad on C, alg=(A,a) a T-algebra, n ∈ ℕ, and X a point of Discrete PUnit. The
carrier of the degree-n algebra emBar(alg)_n(X) equals T(T^n(A)), where T^n is monadPow T n. -/
@[simp]
theorem emBar_obj_A (alg : T.Algebra) (n : ℕ) (X : Discrete PUnit.{1}) :
    (((emBar alg).obj (Opposite.op (SimplexCategory.mk n))).obj X).A =
      T.obj ((monadPow T n).obj alg.A) :=
  rfl

/-- For a monad T on C, T-algebra alg=(A,a), n ∈ ℕ, and X ∈ Discrete PUnit, the structure map of
emBar(alg)_n(X) is μ_{T^n(A)}. Thus the term is the free algebra on the object T^n(A). -/
@[simp]
theorem emBar_obj_a (alg : T.Algebra) (n : ℕ) (X : Discrete PUnit.{1}) :
    (((emBar alg).obj (Opposite.op (SimplexCategory.mk n))).obj X).a =
      T.μ.app ((monadPow T n).obj alg.A) :=
  rfl

/-- Let T be a monad on C, alg=(A,a) a T-algebra, n ∈ ℕ, and i ∈ Fin(n+2). The face emBar_{n+1} →
emBar_n is the two-sided bar face of the free right module and algebra left module. The first
face uses the multiplication action, the last applies free to T^n(a), and interior faces apply
free to multiplication at reversed finite index Fin.rev(i−1). -/
@[simp]
theorem emBar_map_δ_op (alg : T.Algebra) {n : ℕ} (i : Fin (n + 2)) :
    (emBar alg).map (SimplexCategory.δ i).op =
      barFace (T := T) (R := emRightModule) (L := algebraLeftModule alg) n i :=
  twoSidedBar_map_δ_op _ _ _ _

/-- For a monad T on C, T-algebra alg=(A,a), n ∈ ℕ, and i ∈ Fin(n+1), the degeneracy emBar_n →
emBar_{n+1} is the two-sided bar degeneracy. At the unique point it is the free-algebra
functor applied to barEtaAtPos(T,n,i,A), the unit insertion with raw position Fin.rev(i). -/
@[simp]
theorem emBar_map_σ_op (alg : T.Algebra) {n : ℕ} (i : Fin (n + 1)) :
    (emBar alg).map (SimplexCategory.σ i).op =
      barDegeneracy (T := T) (R := emRightModule)
        (L := algebraLeftModule alg) n i :=
  twoSidedBar_map_σ_op _ _ _ _

end EMBar

section EMPairing

/-- For a monad T on C and a T-algebra alg, define emTarget(alg) : Discrete PUnit → T.Algebra to
be the constant functor at alg. This is the target of the Eilenberg–Moore-valued bar
augmentation. -/
abbrev emTarget (alg : T.Algebra) : Discrete PUnit.{1} ⥤ T.Algebra :=
  (Functor.const (Discrete PUnit.{1})).obj alg

/-- Let T be a monad on C and alg=(A,a) a T-algebra. At each discrete point, the zero-degree bar
pairing is the algebra morphism free(A) → alg with underlying map a : T(A) → A. It is a
morphism of algebras because μ_A ≫ a = T(a) ≫ a. -/
def emPairing (alg : T.Algebra) :
    barObj T emRightModule (algebraLeftModule alg) 0 ⟶ emTarget alg where
  app X :=
    { f := alg.a
      h := alg.assoc.symm }
  naturality := fun X Y f => by
    ext
    change T.map (𝟙 _) ≫ alg.a = alg.a ≫ 𝟙 _
    simp

/-- For a monad T on C, T-algebra alg=(A,a), and X ∈ Discrete PUnit, the underlying C-map of
emPairing(alg)_X equals a : T(A) → A. -/
@[simp]
theorem emPairing_f (alg : T.Algebra) (X : Discrete PUnit.{1}) :
    ((emPairing (T := T) alg).app X).f = alg.a :=
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. The zero-degree pairing free(A) → alg is
balanced for the free right T-module and constant algebra left module. Its two degree-one face
composites agree because μ_A ≫ a = T(a) ≫ a, giving a balanced pairing to the constant target
alg. -/
noncomputable def emBalancedPairing (alg : T.Algebra) :
    BalancedPairing T emRightModule (algebraLeftModule alg) :=
  BalancedPairing.mkOfActionEq (emPairing alg) (fun a => by ext; exact alg.assoc)

/-- For a monad T on C, a T-algebra alg=(A,a), and a point X ∈ Discrete PUnit, the underlying map
of the pairing in emBalancedPairing(alg) is a. The balancing data preserve the specified
degree-zero algebra morphism free(A) → alg. -/
@[simp]
theorem emBalancedPairing_pairing_f (alg : T.Algebra) (X : Discrete PUnit.{1}) :
    (((emBalancedPairing (T := T) alg).pairing).app X).f = alg.a :=
  rfl

end EMPairing

section EMAugmented

/-- Let T be a monad on C and alg a T-algebra. The action balanced pairing defines an augmented
simplicial object in Discrete PUnit ⥤ T.Algebra, with underlying object emBar(alg), constant
target alg, and zero-degree augmentation free(alg.A) → alg induced by alg.a. -/
noncomputable def emAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented (Discrete PUnit.{1} ⥤ T.Algebra) :=
  BalancedPairing.toSimplicialAugmented (emBalancedPairing alg)

/-- For a monad T on C and T-algebra alg, the underlying simplicial object of emAugmented(alg)
equals emBar(alg). Its degree-n value is the free algebra on T^n(alg.A). -/
@[simp]
theorem emAugmented_left (alg : T.Algebra) :
    (emAugmented alg).left = emBar alg :=
  rfl

/-- Let T be a monad on C and alg a T-algebra. The target of emAugmented(alg) is emTarget(alg),
the constant functor Discrete PUnit → T.Algebra at alg. -/
@[simp]
theorem emAugmented_right (alg : T.Algebra) :
    (emAugmented alg).right = emTarget alg :=
  rfl

/-- For a monad T on C and T-algebra alg, the augmentation-point functor sends emAugmented(alg) to
the constant diagram emTarget(alg). This is the target object of its augmented free-algebra
bar. -/
@[simp]
theorem emAugmented_point_obj (alg : T.Algebra) :
    (SimplicialObject.Augmented.point.obj (emAugmented alg)) = emTarget alg :=
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. The degree-zero augmentation of
emAugmented(alg) equals emPairing(alg), whose component at the discrete point is the algebra
morphism free(A) → alg with underlying action a. -/
@[simp]
theorem emAugmented_hom_zero (alg : T.Algebra) :
    (emAugmented alg).hom.app (Opposite.op (SimplexCategory.mk 0)) =
      emPairing alg := by
  unfold emAugmented emBalancedPairing
  rw [BalancedPairing.toSimplicialAugmented_hom_app_mk,
    BalancedPairing.toDataHom_app_zero, BalancedPairing.mkOfActionEq_pairing]

end EMAugmented

section EMFunctoriality

/-- Let T be a monad on C and φ : alg → alg′ a T-algebra morphism. The induced natural
transformation emTarget(alg) → emTarget(alg′) between constant Discrete PUnit-indexed algebra
diagrams has component φ at every point. -/
noncomputable def emTargetHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    emTarget alg ⟶ emTarget alg' :=
  (Functor.const (Discrete PUnit.{1})).map φ

/-- For a monad T on C, an algebra morphism φ : alg → alg′, and X ∈ Discrete PUnit, the underlying
C-map of emTargetHom(φ)_X equals φ.f : alg.A → alg′.A. -/
@[simp]
theorem emTargetHom_app_f {alg alg' : T.Algebra} (φ : alg ⟶ alg')
    (X : Discrete PUnit.{1}) :
    (((emTargetHom (T := T) φ).app X)).f = φ.f :=
  rfl

private theorem emTargetHom_id (alg : T.Algebra) :
    emTargetHom (𝟙 alg) = 𝟙 _ := by
  ext X
  rfl

private theorem emTargetHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    emTargetHom φ ≫ emTargetHom ψ = emTargetHom (φ ≫ ψ) := by
  ext X
  rfl

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The degree-zero bar map with
identity on the free right module and algebra left-module map φ, followed by the pairing to
alg′, equals the pairing to alg followed by the constant target map φ. On carriers the
equality is T(φ.f) ≫ alg′.a = alg.a ≫ φ.f. -/
theorem em_hq {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    barMap (𝟙 emRightModule) (algebraLeftModuleHom φ) 0 ≫
        (emBalancedPairing alg').pairing =
      (emBalancedPairing alg).pairing ≫ emTargetHom φ := by
  ext X
  simp only [NatTrans.comp_app, barMap_app, algebraLeftModuleHom_f_app,
    Algebra.comp_f, emRightModule_functor_map_f, Algebra.id_f, NatTrans.id_app,
    emBalancedPairing_pairing_f, Category.comp_id]
  exact φ.h

/-- For a monad T on C and an algebra morphism φ : alg → alg′, the identity free-right-module map
and the algebra left-module map induce emAugmented(alg) → emAugmented(alg′). Its simplicial
part is the two-sided bar map, and its target part is the constant diagram morphism at φ. The
action-compatibility equation makes it an augmented map. -/
noncomputable def emHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    emAugmented alg ⟶ emAugmented alg' :=
  BalancedPairing.toSimplicialAugmentedMap (emBalancedPairing alg)
    (emBalancedPairing alg') (𝟙 emRightModule) (algebraLeftModuleHom φ)
    (emTargetHom φ) (em_hq φ)

/-- Let T be a monad on C and alg a T-algebra. The augmented free-bar map emHom(𝟙_alg) equals the
identity of emAugmented(alg), on both simplicial terms and the constant algebra target. -/
theorem emHom_id (alg : T.Algebra) :
    emHom (𝟙 alg) = 𝟙 (emAugmented alg) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have e1 : (emHom (𝟙 alg)).left =
        twoSidedBarHom (𝟙 emRightModule) (𝟙 (algebraLeftModule alg)) := by
      simp only [emHom, algebraLeftModuleHom_id]
      rfl
    have e2 : twoSidedBarHom (𝟙 emRightModule) (𝟙 (algebraLeftModule alg)) =
        𝟙 (twoSidedBar T emRightModule (algebraLeftModule alg)) :=
      twoSidedBarHom_id _ _
    have e3 : (𝟙 (twoSidedBar T emRightModule (algebraLeftModule alg))) =
        𝟙 (emAugmented alg).left :=
      rfl
    exact e1.trans (e2.trans e3)
  · have e1r : (emHom (𝟙 alg)).right = emTargetHom (𝟙 alg) := by
      simp only [emHom]
      rfl
    have e2r : emTargetHom (𝟙 alg) = 𝟙 (emTarget alg) :=
      emTargetHom_id alg
    have e3r : (𝟙 (emTarget alg)) = 𝟙 (emAugmented alg).right :=
      rfl
    exact e1r.trans (e2r.trans e3r)

/-- For a monad T on C and algebra morphisms φ : alg₁ → alg₂, ψ : alg₂ → alg₃, emHom(φ) ≫ emHom(ψ)
= emHom(φ ≫ ψ). This is equality of augmented simplicial morphisms with values in Discrete
PUnit ⥤ T.Algebra. -/
theorem emHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    emHom φ ≫ emHom ψ = emHom (φ ≫ ψ) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have f1 : (emHom φ ≫ emHom ψ).left =
        twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom φ) ≫
          twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom ψ) := by
      rw [Comma.comp_left]
      simp only [emHom]
      rfl
    have f2 : twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom φ) ≫
        twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom ψ) =
        twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom (φ ≫ ψ)) := by
      rw [twoSidedBarHom_comp, Category.id_comp, algebraLeftModuleHom_comp]
    have f3 : twoSidedBarHom (𝟙 emRightModule)
        (algebraLeftModuleHom (φ ≫ ψ)) = (emHom (φ ≫ ψ)).left := by
      simp only [emHom]
      rfl
    exact f1.trans (f2.trans f3)
  · have g1 : (emHom φ ≫ emHom ψ).right =
        emTargetHom φ ≫ emTargetHom ψ := by
      rw [Comma.comp_right]
      simp only [emHom]
      rfl
    have g2 : emTargetHom φ ≫ emTargetHom ψ = emTargetHom (φ ≫ ψ) :=
      emTargetHom_comp φ ψ
    have g3 : emTargetHom (φ ≫ ψ) = (emHom (φ ≫ ψ)).right := by
      simp only [emHom]
      rfl
    exact g1.trans (g2.trans g3)

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The underlying simplicial map of
emHom(φ) equals twoSidedBarHom of the identity free right-module map and
algebraLeftModuleHom(φ). In degree n its value is the free-algebra map of T^n(φ.f). -/
theorem emHom_left {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emHom φ).left =
      twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom φ) := by
  simp only [emHom]
  rfl

/-- For a monad T on C and an algebra morphism φ : alg → alg′, the augmentation-target component
of emHom(φ) equals emTargetHom(φ), the constant natural transformation with component φ. -/
theorem emHom_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emHom φ).right = emTargetHom φ := by
  simp only [emHom]
  rfl

end EMFunctoriality

section UnderlyingComparison

/-- Let T be a monad on C and alg=(A,a) a T-algebra. Postcompose the free-algebra right T-module
with T.forget and pair it with the constant left module of alg. The resulting C-valued
balanced pairing has constant target A and component a : T(A) → A. Its balancing equation is
μ_A ≫ a = T(a) ≫ a. -/
noncomputable abbrev emUnderlyingPairing (alg : T.Algebra) :
    BalancedPairing T (emRightModule.postcomp T.forget)
      (algebraLeftModule alg) :=
  BarRegularContraction.regularBalancedPairing (algebraLeftModule alg)

/-- For a monad T on C, a T-algebra alg=(A,a), and a point of Discrete PUnit, the component of
emUnderlyingPairing(alg) equals a : T(A) → A. -/
@[simp]
theorem emUnderlyingPairing_pairing_app (alg : T.Algebra)
    (a : Discrete PUnit.{1}) :
    ((emUnderlyingPairing (T := T) alg).pairing).app a = alg.a :=
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. Evaluate the balanced bar of the forgotten
free right module and the algebra left module at the unique discrete point. This defines an
augmented simplicial object of C with degree-n term T(T^n(A)), target A, and zero-degree
augmentation a. -/
noncomputable abbrev emUnderlyingAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented C :=
  resolutionAugmented alg

/-- For a monad T on C and T-algebra alg=(A,a), the augmentation target of
emUnderlyingAugmented(alg) equals A. This is the evaluated constant target of the action
pairing. -/
@[simp]
theorem emUnderlyingAugmented_point (alg : T.Algebra) :
    (emUnderlyingAugmented alg).right = alg.A :=
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. Define emUnderlyingBar(alg) by the two-sided
bar of the free right module postcomposed with T.forget and the constant left module of alg,
evaluated at the unique point. Its degree-n object is T(T^n(A)), with faces and degeneracies
inherited from these actions. -/
noncomputable abbrev emUnderlyingBar (alg : T.Algebra) : SimplicialObject C :=
  resolutionBar alg

/-- Let T be a monad on C and alg a T-algebra. The underlying simplicial object of
emUnderlyingAugmented(alg) equals emUnderlyingBar(alg), the evaluated bar of the forgotten
free right module and algebra left module. -/
@[simp]
theorem emUnderlyingAugmented_left (alg : T.Algebra) :
    (emUnderlyingAugmented alg).left = emUnderlyingBar alg :=
  rfl

/-- For a monad T on C and T-algebra alg=(A,a), the zero-degree augmentation of
emUnderlyingAugmented(alg) equals a : T(A) → A. -/
@[simp]
theorem emUnderlyingAugmented_hom_zero (alg : T.Algebra) :
    (emUnderlyingAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = alg.a :=
  resolutionAugmented_hom_zero alg

/-- Let T be a monad on C and alg a T-algebra. The module isomorphism between the forgotten free
right module and the regular right module, together with the identity algebra left-module
comparison, induces emUnderlyingBar(alg) ≅ resolutionBar(alg). The target is the regular-right
two-sided bar B(T,T,alg.A) with its algebra action. -/
noncomputable def emUnderlyingBarIso (alg : T.Algebra) :
    emUnderlyingBar alg ≅ resolutionBar alg :=
  Functor.isoWhiskerRight (twoSidedBarIso emModuleIso (Iso.refl _)) resolutionEvalPoint

/-- For a monad T on C, T-algebra alg, and n ∈ ℕ, the forward degree-n component of
emUnderlyingBarIso(alg) is evaluation at the unique point of barMap(emModuleIso.hom,id_L,n),
where L is the algebra left module. This specifies the component induced by the
forgotten-free-to-regular module isomorphism. -/
@[simp]
theorem emUnderlyingBarIso_hom_app (alg : T.Algebra) (n : ℕ) :
    (emUnderlyingBarIso alg).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
      resolutionEvalPoint.map (barMap emModuleIso.hom (Iso.refl _).hom n) :=
  rfl

/-- Let T be a monad on C, alg a T-algebra, and n ∈ ℕ. The inverse degree-n component of
emUnderlyingBarIso(alg) is evaluation of barMap(emModuleIso.inv,id_L,n) at the unique point,
with L the algebra left module. This is the bar map of the inverse regular-to-forgotten-free
module comparison. -/
@[simp]
theorem emUnderlyingBarIso_inv_app (alg : T.Algebra) (n : ℕ) :
    (emUnderlyingBarIso alg).inv.app
      (Opposite.op (SimplexCategory.mk n)) =
      resolutionEvalPoint.map (barMap emModuleIso.inv (Iso.refl _).inv n) :=
  rfl

/-- Let C be a category, Q : Discrete PUnit ⥤ C a diagram, and a a point of the discrete index.
The degree-zero component of the constant simplicial-data map induced by the reflexive
isomorphism of Q, evaluated at a, is 𝟙_{Q(a)}. -/
@[simp]
theorem emConstRefl_app (Q : Discrete PUnit.{1} ⥤ C)
    (a : Discrete PUnit.{1}) :
    ((SimplicialObject.Data.constFunctor.map (Iso.refl Q).hom).app 0).app a =
      𝟙 _ :=
  rfl

/-- Let T be a monad on C, L a left T-module indexed by Discrete PUnit, and a a discrete point.
The underlying component at a of the reflexive module isomorphism of L is the identity of
L(a). -/
@[simp]
theorem emModRefl_f_app (L : LeftModule (Discrete PUnit.{1}) T)
    (a : Discrete PUnit.{1}) :
    ((((Iso.refl L).hom).f).app a) = 𝟙 _ :=
  rfl

/-- For a monad T on C and T-algebra alg, the bar-data map induced by emModuleIso and the identity
left-module map, followed by the regular-right action augmentation, equals the forgotten-free
pairing augmentation followed by the constant identity target map. Thus the data comparison
preserves the augmentation to alg.A. -/
theorem emDataAug_w (alg : T.Algebra) :
    (𝟭 (SimplicialObject.Data (Discrete PUnit.{1} ⥤ C))).map
        (barDataIso emModuleIso (Iso.refl _)).hom ≫
        (BarRegularContraction.regularBalancedPairing
          (algebraLeftModule alg)).toDataHom =
      (emUnderlyingPairing alg).toDataHom ≫
        SimplicialObject.Data.constFunctor.map (Iso.refl _).hom := by
  apply SimplicialObject.Data.hom_eq_of_app_zero_eq
  ext a
  change ((T.map (𝟙 _) ≫ 𝟙 _) ≫ alg.a) = (alg.a ≫ 𝟙 _)
  simp only [Functor.map_id, Category.id_comp, Category.comp_id]

/-- Let T be a monad on C and alg a T-algebra. The bar-data isomorphism induced by emModuleIso and
the identity algebra left-module map gives an isomorphism from the augmented data of
emUnderlyingPairing(alg) to the regular-right balanced augmentation. Its target component is
the identity of the constant carrier diagram. -/
noncomputable def emDataAugIso (alg : T.Algebra) :
    (emUnderlyingPairing alg).toAugmented ≅
      (BarRegularContraction.regularBalancedPairing
        (algebraLeftModule alg)).toAugmented :=
  Comma.isoMk (barDataIso emModuleIso (Iso.refl _)) (Iso.refl _)
    (emDataAug_w alg)

/-- For a monad T on C and T-algebra alg, evaluating the augmented-data comparison gives
emUnderlyingAugmented(alg) ≅ resolutionAugmented(alg). The comparison is induced by the
forgotten-free-to-regular right-module isomorphism and the identity left-module and target
comparisons, so it preserves both simplicial operators and the algebra augmentation. -/
noncomputable def emAugmentedIso (alg : T.Algebra) :
    emUnderlyingAugmented alg ≅ resolutionAugmented alg :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).mapIso
    (SimplicialObject.Data.Augmented.toSimplicialFunctor.mapIso (emDataAugIso alg))

/-- For a monad T on C and a T-algebra alg=(A,a), the zero-degree augmentations of
emUnderlyingAugmented(alg) and resolutionAugmented(alg) are equal. Both maps are the algebra
action a : T(A) → A. -/
theorem emUnderlying_hom_zero_eq (alg : T.Algebra) :
    (emUnderlyingAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) =
      (resolutionAugmented alg).hom.app
        (Opposite.op (SimplexCategory.mk 0)) :=
  rfl

/-- Let T be a monad on C and alg a T-algebra. There is an isomorphism emUnderlyingBar(alg) ≅
resolutionAugmented(alg).left. It compares the bar of the forgotten free right module with the
underlying simplicial object of the regular-right monadic augmentation. -/
noncomputable def emUnderlyingBar_iso_resLeft (alg : T.Algebra) :
    emUnderlyingBar alg ≅ (resolutionAugmented alg).left := by
  exact emUnderlyingBarIso alg

/-- For a monad T on C and algebra morphism φ : alg → alg′, define a natural transformation
between the constant target diagrams of emUnderlyingPairing(alg) and
emUnderlyingPairing(alg′). At every point of Discrete PUnit its component is φ.f : alg.A →
alg′.A. -/
noncomputable def emUnderlyingTargetHom {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') :
    (emUnderlyingPairing alg).target ⟶ (emUnderlyingPairing alg').target where
  app _ := φ.f
  naturality _ _ _ := by
    change (𝟙 alg.A) ≫ φ.f = φ.f ≫ (𝟙 alg'.A)
    simp

/-- Let T be a monad on C, φ : alg → alg′ an algebra morphism, and X ∈ Discrete PUnit. The
component emUnderlyingTargetHom(φ)_X equals φ.f. -/
@[simp]
theorem emUnderlyingTargetHom_app {alg alg' : T.Algebra} (φ : alg ⟶ alg')
    (X : Discrete PUnit.{1}) :
    ((emUnderlyingTargetHom (T := T) φ).app X) = φ.f :=
  rfl

/-- For a monad T on C and algebra morphism φ : alg → alg′, the degree-zero bar map with identity
forgotten right-module map and left-module map φ commutes with the action pairings. Its
equation is b_0(φ) ≫ pairing_alg′ = pairing_alg ≫ target(φ), whose carrier form is T(φ.f) ≫
alg′.a = alg.a ≫ φ.f. -/
theorem emUnderlying_hq {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    barMap (𝟙 (emRightModule.postcomp T.forget)) (algebraLeftModuleHom φ) 0 ≫
        (emUnderlyingPairing alg').pairing =
      (emUnderlyingPairing alg).pairing ≫ emUnderlyingTargetHom φ := by
  ext X
  simp only [NatTrans.comp_app, barMap_app]
  simp only [Functor.id_map]
  simp only [algebraLeftModuleHom_f_app, Algebra.id_f,
    NatTrans.id_app, Category.comp_id,
    emUnderlyingTargetHom_app, emUnderlyingPairing_pairing_app]
  exact φ.h

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The two-sided bar map with
identity on the forgotten free right module and algebra left-module map φ, together with the
constant carrier target map, gives emUnderlyingAugmented(alg) → emUnderlyingAugmented(alg′)
after evaluation at the unique point. -/
noncomputable abbrev emUnderlyingHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    emUnderlyingAugmented alg ⟶ emUnderlyingAugmented alg' :=
  resolutionHom φ

/-- For a monad T on C and algebra morphism φ : alg → alg′, the underlying simplicial map of
emUnderlyingHom(φ) equals algebraBarHom of the identity forgotten right-module map and φ. Its
degree-n component acts on the algebra carrier by T(T^n(φ.f)). -/
theorem emUnderlyingHom_left {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emUnderlyingHom φ).left =
      algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) φ :=
  resolutionHom_left φ

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The augmentation-target
component of emUnderlyingHom(φ) equals the carrier morphism φ.f : alg.A → alg′.A. -/
theorem emUnderlyingHom_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emUnderlyingHom φ).right = φ.f :=
  resolutionHom_right φ

/-- For a monad T on C and T-algebra alg, emUnderlyingHom(𝟙_alg) equals the identity augmented map
of emUnderlyingAugmented(alg). This includes its simplicial component and its algebra-carrier
target. -/
theorem emUnderlyingHom_id (alg : T.Algebra) :
    emUnderlyingHom (𝟙 alg) = 𝟙 (emUnderlyingAugmented alg) :=
  resolutionHom_id alg

/-- Let T be a monad on C and φ : alg₁ → alg₂, ψ : alg₂ → alg₃ algebra morphisms. Then
emUnderlyingHom(φ) ≫ emUnderlyingHom(ψ) = emUnderlyingHom(φ ≫ ψ), as augmented simplicial maps
of C. -/
theorem emUnderlyingHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    emUnderlyingHom φ ≫ emUnderlyingHom ψ = emUnderlyingHom (φ ≫ ψ) :=
  resolutionHom_comp φ ψ

/-- For a monad T on C and algebra morphism φ : alg → alg′, the simplicial comparison
e=emUnderlyingBarIso satisfies emUnderlyingHom(φ).left ≫ e_alg′.hom = e_alg.hom ≫
resolutionHom(φ).left. It identifies the forgotten-free-module bar maps with the regular-right
monadic bar maps. -/
theorem emNaturality_left {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emUnderlyingHom φ).left ≫ (emUnderlyingBarIso alg').hom =
      (emUnderlyingBarIso alg).hom ≫ (resolutionHom φ).left := by
  rw [emUnderlyingHom_left]
  change Functor.whiskerRight
      (twoSidedBarHom (𝟙 (emRightModule.postcomp T.forget))
        (algebraLeftModuleHom φ)) resolutionEvalPoint ≫
      Functor.whiskerRight (twoSidedBarHom emModuleIso.hom (Iso.refl _).hom)
        resolutionEvalPoint =
    Functor.whiskerRight (twoSidedBarHom emModuleIso.hom (Iso.refl _).hom)
        resolutionEvalPoint ≫
      Functor.whiskerRight
        (twoSidedBarHom (𝟙 (RightModule.regular T))
          (algebraLeftModuleHom φ)) resolutionEvalPoint
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp,
    twoSidedBarHom_comp, twoSidedBarHom_comp, Iso.refl_hom, Iso.refl_hom,
    Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The target components of
emUnderlyingHom(φ) and resolutionHom(φ) are equal. Both are the underlying map φ.f between the
algebra carriers. -/
theorem emNaturality_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emUnderlyingHom φ).right = (resolutionHom φ).right :=
  rfl

/-- For a monad T on C and a T-algebra alg, the simplicial projection of emAugmentedIso(alg).hom
equals emUnderlyingBarIso(alg).hom. Thus the augmented comparison retains the specified
forgotten-free-to-regular bar isomorphism. -/
@[simp]
theorem emAugmentedIso_hom_left (alg : T.Algebra) :
    (emAugmentedIso alg).hom.left = (emUnderlyingBarIso alg).hom :=
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. The augmentation-target component of
emAugmentedIso(alg).hom is the identity on A. Both augmented bar descriptions use the same
algebra carrier as target. -/
@[simp]
theorem emAugmentedIso_hom_right (alg : T.Algebra) :
    (emAugmentedIso alg).hom.right = 𝟙 _ := by
  have hA : (emAugmentedIso alg).hom.right =
      resolutionEvalPoint.map ((emDataAugIso alg).hom.right) := rfl
  have hB : (emDataAugIso alg).hom.right =
      𝟙 (emUnderlyingPairing alg).toAugmented.right := rfl
  rw [hA, hB]
  exact Functor.map_id _ _

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The augmented isomorphism
e=emAugmentedIso satisfies emUnderlyingHom(φ) ≫ e_alg′.hom = e_alg.hom ≫ resolutionHom(φ). The
equality includes both the simplicial naturality square and the identity comparisons on
algebra-carrier targets. -/
theorem emAugmented_naturality {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    emUnderlyingHom φ ≫ (emAugmentedIso alg').hom =
      (emAugmentedIso alg).hom ≫ resolutionHom φ := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · rw [Comma.comp_left, Comma.comp_left, emAugmentedIso_hom_left,
      emAugmentedIso_hom_left]
    exact emNaturality_left φ
  · rw [Comma.comp_right, Comma.comp_right, emAugmentedIso_hom_right,
      emAugmentedIso_hom_right, emNaturality_right φ]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

end UnderlyingComparison

section LiteralComparison

/-- For a monad T on C, define evaluation (Discrete PUnit ⥤ T.Algebra) → T.Algebra at the unique
discrete point. It sends a diagram to its value at that point and a natural transformation to
its corresponding algebra-morphism component. -/
noncomputable abbrev emEvalAlgebra : (Discrete PUnit.{1} ⥤ T.Algebra) ⥤ T.Algebra :=
  resolutionEvalPoint (C := T.Algebra)

/-- Let T be a monad on C and alg a T-algebra. Evaluate emAugmented(alg) at the unique discrete
point to obtain an augmented simplicial object of T.Algebra. Its target is alg, its degree-n
term is free(T^n(alg.A)), and its zero-degree augmentation is the algebra action pairing. -/
noncomputable def emEvaluatedAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented T.Algebra :=
  (SimplicialObject.Augmented.whiskeringObj _ _ emEvalAlgebra).obj (emAugmented alg)

/-- For a monad T on C and T-algebra alg, the underlying simplicial object of
emEvaluatedAugmented(alg) equals emBar(alg) followed by evaluation at the unique discrete
point in T.Algebra. -/
@[simp]
theorem emEvaluatedAugmented_left (alg : T.Algebra) :
    (emEvaluatedAugmented alg).left = emBar alg ⋙ emEvalAlgebra := by
  unfold emEvaluatedAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_left]
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. Apply T.forget to emEvaluatedAugmented(alg)
to obtain an augmented simplicial object of C. Its degree-n carrier is T(T^n(A)) and its
augmentation target is A. This evaluated-and-forgotten construction is compared with the bar
of the forgotten right module by emLiteralIso. -/
noncomputable def emLiteralAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj _ _ T.forget).obj
    (emEvaluatedAugmented alg)

/-- For a monad T on C and T-algebra alg, the simplicial object underlying emLiteralAugmented(alg)
equals emEvaluatedAugmented(alg).left followed by T.forget. Thus each free-algebra bar term is
replaced by its underlying C-object. -/
@[simp]
theorem emLiteralAugmented_left (alg : T.Algebra) :
    (emLiteralAugmented alg).left =
      (emEvaluatedAugmented alg).left ⋙ T.forget := by
  unfold emLiteralAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_left]
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. The augmentation target of
emLiteralAugmented(alg), obtained by evaluating the algebra-valued bar and then forgetting, is
exactly A. -/
@[simp]
theorem emLiteralAugmented_point (alg : T.Algebra) :
    (emLiteralAugmented alg).right = alg.A :=
  rfl

/-- Let T be a monad on C and alg=(A,a) a T-algebra. The zero-degree augmentation of
emLiteralAugmented(alg) equals a : T(A) → A, obtained by evaluating the free-algebra action
pairing and forgetting. -/
@[simp]
theorem emLiteralAugmented_hom_zero (alg : T.Algebra) :
    (emLiteralAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = alg.a := by
  unfold emLiteralAugmented emEvaluatedAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    emAugmented_hom_zero]
  rfl

/-- For a monad T on C, evaluation of a Discrete PUnit-indexed algebra diagram followed by
T.forget is naturally isomorphic to postcomposing the diagram by T.forget and then evaluating
at the unique point. Both send a diagram H to its underlying object U(H(*)), and the
comparison has identity components. -/
noncomputable def emEvalForgetIso :
    (emEvalAlgebra ⋙ T.forget) ≅
      (functorPostcompOuter T.forget ⋙ resolutionEvalPoint) :=
  Iso.refl _

/-- Let T be a monad on C and alg a T-algebra. The simplicial object underlying
emLiteralAugmented(alg) is isomorphic to emUnderlyingBar(alg). The comparison commutes
evaluation with forgetting and then uses the two-sided bar isomorphism for postcomposition of
the free right module by T.forget. -/
noncomputable def emLiteralBarIso (alg : T.Algebra) :
    (emLiteralAugmented alg).left ≅ emUnderlyingBar alg :=
  (Functor.associator
    (twoSidedBar T emRightModule (algebraLeftModule alg))
    emEvalAlgebra T.forget) ≪≫
    (Functor.isoWhiskerLeft
      (twoSidedBar T emRightModule (algebraLeftModule alg))
      emEvalForgetIso) ≪≫
    (Functor.associator
      (twoSidedBar T emRightModule (algebraLeftModule alg))
      (functorPostcompOuter T.forget) resolutionEvalPoint).symm ≪≫
    (Functor.isoWhiskerRight
      (twoSidedBarPostcompWhiskerIso T.forget emRightModule
        (algebraLeftModule alg))
      resolutionEvalPoint)

/-- For a monad T on C, T-algebra alg, and simplex Δ, the forward associator for the composite of
its two-sided free bar, point evaluation in T.Algebra, and T.forget has identity component at
Δ. Both parenthesizations give the same evaluated-and-forgotten bar term. -/
private theorem emLiteralAssoc_hom_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.associator
      (twoSidedBar T emRightModule (algebraLeftModule alg))
      emEvalAlgebra T.forget).hom.app Δ =
      𝟙 _ :=
  rfl

/-- Let T be a monad on C, alg a T-algebra, and Δ a simplex. The inverse associator for the
composite of the free bar, postcomposition by T.forget, and point evaluation in C has identity
component at Δ. -/
private theorem emLiteralAssocSymm_hom_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.associator
      (twoSidedBar T emRightModule (algebraLeftModule alg))
      (functorPostcompOuter T.forget) resolutionEvalPoint).symm.hom.app Δ =
      𝟙 _ :=
  rfl

/-- For a monad T on C, T-algebra alg, and simplex Δ, whiskering the evaluation–forgetting
commutation isomorphism by the free-algebra two-sided bar gives an isomorphism whose forward
Δ-component is the identity. -/
private theorem emLiteralWhiskerComm_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.isoWhiskerLeft
      (twoSidedBar T emRightModule (algebraLeftModule alg))
      emEvalForgetIso).hom.app Δ =
      𝟙 _ :=
  rfl

/-- Let C be a category, F,G : Discrete PUnit ⥤ C, and η : F → G a natural transformation.
Evaluation at the unique point sends η to its component η_* : F(*) → G(*). -/
private theorem emEvalPoint_map_app {F G : Discrete PUnit.{1} ⥤ C}
    (η : F ⟶ G) :
    resolutionEvalPoint.map η = η.app (Discrete.mk PUnit.unit) :=
  rfl

/-- For a monad T on C, diagrams F,G : Discrete PUnit ⥤ T.Algebra, and natural transformation η :
F → G, emEvalAlgebra sends η to its algebra-morphism component at the unique point. -/
private theorem emEvalAlgebra_map_app {F G : Discrete PUnit.{1} ⥤ T.Algebra}
    (η : F ⟶ G) :
    emEvalAlgebra.map η = η.app (Discrete.mk PUnit.unit) :=
  rfl

/-- Let T be a monad on C, alg a T-algebra, n ∈ ℕ, and a point of Discrete PUnit. The underlying
C-map of the first face d_0 : B_{n+1} → B_n in the algebra-valued bar equals the first face in
the bar of the right module postcomposed with T.forget. This equality retains the fixed
first-face index 0. -/
private theorem emDataForget_face_agree (alg : T.Algebra) (n : ℕ)
    (a : Discrete PUnit.{1}) :
    ((((barData T emRightModule (algebraLeftModule alg)).δ
      (0 : Fin (n + 2))).app a).f) =
      (((barData T (emRightModule.postcomp T.forget)
        (algebraLeftModule alg)).δ (0 : Fin (n + 2))).app a) := by
  rw [barData_δ_app, barData_δ_app]
  exact (barFaceApp_postcomp T.forget emRightModule
    (algebraLeftModule alg) n _ a).symm

/-- For a monad T on C, T-algebra alg, n ∈ ℕ, and discrete point X, the underlying morphism of the
degree-n balanced augmentation of the free-algebra bar equals the degree-n augmentation of
emUnderlyingPairing(alg) at X. Thus forgetting preserves the entire augmentation data in every
degree. -/
private theorem emDataForget_agree (alg : T.Algebra) (n : ℕ)
    (a : Discrete PUnit.{1}) :
    (((((emBalancedPairing (T := T) alg).toDataHom.app n).app a)).f) =
      ((((emUnderlyingPairing (T := T) alg).toDataHom.app n).app a)) := by
  induction n with
  | zero =>
    simp only [BalancedPairing.toDataHom_app_zero, emBalancedPairing_pairing_f,
      emUnderlyingPairing_pairing_app] ; rfl
  | succ n ih =>
    simp only [BalancedPairing.toDataHom_app_succ, NatTrans.comp_app,
      Algebra.comp_f, emDataForget_face_agree alg n a, ih] ; rfl

/-- Let T be a monad on C, alg a T-algebra, and Δ ∈ SimplexCategoryᵒᵖ. The forward Δ-component of
emLiteralBarIso(alg) is the identity. It identifies the evaluated-and-forgotten free bar with
the bar of the forgotten right module on their common degree object. -/
@[simp]
theorem emLiteralBarIso_hom_app (alg : T.Algebra) (Δ : SimplexCategoryᵒᵖ) :
    (emLiteralBarIso alg).hom.app Δ = 𝟙 _ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ]
  have hdecomp : (emLiteralBarIso alg).hom =
      (Functor.associator
        (twoSidedBar T emRightModule (algebraLeftModule alg))
        emEvalAlgebra T.forget).hom ≫
      (Functor.isoWhiskerLeft
        (twoSidedBar T emRightModule (algebraLeftModule alg))
        emEvalForgetIso).hom ≫
      (Functor.associator
        (twoSidedBar T emRightModule (algebraLeftModule alg))
        (functorPostcompOuter T.forget)
        resolutionEvalPoint).symm.hom ≫
      (Functor.isoWhiskerRight
        (twoSidedBarPostcompWhiskerIso T.forget emRightModule
          (algebraLeftModule alg))
        resolutionEvalPoint).hom := rfl
  rw [hdecomp, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    emLiteralAssoc_hom_app, emLiteralWhiskerComm_app,
    emLiteralAssocSymm_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, emEvalPoint_map_app,
    twoSidedBarPostcompWhiskerIso_hom_app_app_id]
  change 𝟙 (((twoSidedBar T emRightModule (algebraLeftModule alg) ⋙
      emEvalAlgebra ⋙ T.forget).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)))) ≫
    𝟙 (((twoSidedBar T emRightModule (algebraLeftModule alg) ⋙
      emEvalAlgebra ⋙ T.forget).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)))) ≫
    𝟙 (((twoSidedBar T emRightModule (algebraLeftModule alg) ⋙
      emEvalAlgebra ⋙ T.forget).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)))) ≫
    𝟙 (((twoSidedBar T emRightModule (algebraLeftModule alg) ⋙
      emEvalAlgebra ⋙ T.forget).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)))) =
    𝟙 (((twoSidedBar T emRightModule (algebraLeftModule alg) ⋙
      emEvalAlgebra ⋙ T.forget).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))))
  simp only [Category.comp_id]

/-- For a monad T on C, T-algebra alg, and n ∈ ℕ, the augmentation maps of emLiteralAugmented(alg)
and emUnderlyingAugmented(alg) at the opposite simplex [n] are equal. These maps come
respectively from evaluating and forgetting the algebra bar and from the
forgotten-right-module action pairing. -/
private theorem emLiteralHomAgree_app (alg : T.Algebra) (n : ℕ) :
    (emLiteralAugmented alg).hom.app (Opposite.op (SimplexCategory.mk n)) =
      (emUnderlyingAugmented alg).hom.app
        (Opposite.op (SimplexCategory.mk n)) := by
  unfold emLiteralAugmented emEvaluatedAugmented emAugmented
    emUnderlyingAugmented resolutionAugmented
  simp only [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    BalancedPairing.toSimplicialAugmented_hom_app_mk]
  change T.forget.map (emEvalAlgebra.map
      ((emBalancedPairing alg).toDataHom.app n)) =
    resolutionEvalPoint.map ((emUnderlyingPairing alg).toDataHom.app n)
  rw [emEvalAlgebra_map_app, emEvalPoint_map_app]
  exact emDataForget_agree alg n _

/-- Let T be a monad on C and alg a T-algebra. The simplicial comparison emLiteralBarIso(alg),
together with the identity on the augmentation target alg.A, defines emLiteralAugmented(alg) ≅
emUnderlyingAugmented(alg). The equality of their augmentation components makes this an
isomorphism of augmented simplicial objects. -/
noncomputable def emLiteralIso (alg : T.Algebra) :
    emLiteralAugmented alg ≅ emUnderlyingAugmented alg :=
  Comma.isoMk (emLiteralBarIso alg) (Iso.refl _) (by
    ext Δ
    simp only [NatTrans.comp_app, Functor.id_map]
    have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
      obtain ⟨d⟩ := Δ
      exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
    rw [hΔ, emLiteralHomAgree_app]
    have h1 : (emLiteralBarIso alg).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) =
        𝟙 ((emUnderlyingAugmented alg).left.obj
          (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) :=
      emLiteralBarIso_hom_app alg _
    rw [h1]
    simp only [Functor.id_obj, SimplexCategory.mk_len, Opposite.op_unop,
      emUnderlyingAugmented_point, Functor.const_obj_obj,
      emUnderlyingAugmented_left, emLiteralAugmented_point, Iso.refl_hom,
      Functor.map_id, NatTrans.id_app]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- For a monad T on C and T-algebra alg, composing emLiteralIso(alg) with emAugmentedIso(alg)
gives an isomorphism emLiteralAugmented(alg) ≅ resolutionAugmented(alg). It compares the
evaluated-and-forgotten Eilenberg–Moore bar with the regular-right monadic bar augmented to
the algebra carrier. -/
noncomputable def emLiteralResolutionIso (alg : T.Algebra) :
    emLiteralAugmented alg ≅ resolutionAugmented alg :=
  emLiteralIso alg ≪≫ emAugmentedIso alg

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. Evaluate the augmented free-bar
map emHom(φ) at the unique point and apply T.forget. This gives an augmented map
emLiteralAugmented(alg) → emLiteralAugmented(alg′). -/
noncomputable def emLiteralHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    emLiteralAugmented alg ⟶ emLiteralAugmented alg' :=
  (SimplicialObject.Augmented.whiskeringObj _ _ T.forget).map
    ((SimplicialObject.Augmented.whiskeringObj _ _ emEvalAlgebra).map
      (emHom φ))

/-- For a monad T on C and algebra morphism φ : alg → alg′, the simplicial part of emLiteralHom(φ)
is the two-sided bar map with identity free right-module component and algebra left-module
component φ, followed by point evaluation in T.Algebra and T.forget. Thus both whiskerings act
on the same bar-map components. -/
theorem emLiteralHom_left {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emLiteralHom φ).left =
      Functor.whiskerRight
        (Functor.whiskerRight
          (twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom φ))
          emEvalAlgebra)
        T.forget :=
  rfl

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The augmentation-target
component of emLiteralHom(φ) equals φ.f : alg.A → alg′.A. -/
theorem emLiteralHom_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emLiteralHom φ).right = φ.f :=
  rfl

/-- For a monad T on C and T-algebra alg, emLiteralHom(𝟙_alg) equals the identity of
emLiteralAugmented(alg). This includes the simplicial bar and its augmentation target. -/
theorem emLiteralHom_id (alg : T.Algebra) :
    emLiteralHom (𝟙 alg) = 𝟙 (emLiteralAugmented alg) := by
  dsimp only [emLiteralHom, emEvaluatedAugmented, emLiteralAugmented]
  rw [emHom_id, Functor.map_id, Functor.map_id]

/-- Let T be a monad on C and algebra morphisms φ : alg₁ → alg₂, ψ : alg₂ → alg₃. Then
emLiteralHom(φ) ≫ emLiteralHom(ψ) = emLiteralHom(φ ≫ ψ) as augmented simplicial maps of C. -/
theorem emLiteralHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    emLiteralHom φ ≫ emLiteralHom ψ = emLiteralHom (φ ≫ ψ) := by
  dsimp only [emLiteralHom, emEvaluatedAugmented, emLiteralAugmented]
  rw [← Functor.map_comp, ← Functor.map_comp, emHom_comp]

/-- For a monad T on C and a T-algebra alg=(A,a), the target component of
emLiteralResolutionIso(alg).hom is the identity on A. The evaluated-and-forgotten and regular
monadic augmentations have the same algebra-carrier target. -/
theorem emLiteralResolutionIso_hom_right (alg : T.Algebra) :
    (emLiteralResolutionIso alg).hom.right = 𝟙 _ := by
  have hA : (emLiteralResolutionIso alg).hom =
      (emLiteralIso alg).hom ≫ (emAugmentedIso alg).hom := rfl
  rw [hA, Comma.comp_right]
  change (Iso.refl (emLiteralAugmented alg).right).hom ≫
      resolutionEvalPoint.map
        ((Iso.refl (emUnderlyingPairing alg).toAugmented.right).hom) = 𝟙 _
  simp only [Iso.refl_hom, Functor.map_id]
  exact Category.id_comp _

/-- Let T be a monad on C, alg a T-algebra, and Δ a simplex. The forward Δ-component of
emUnderlyingBarIso(alg) is the identity. The forgotten free right module and regular right
module both have carrier functor T and action μ. -/
private theorem emUnderlyingBarIso_hom_app_id (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (emUnderlyingBarIso alg).hom.app Δ = 𝟙 _ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ, emUnderlyingBarIso_hom_app, emEvalPoint_map_app, barMap_app,
    emModuleIso_hom_f_app, emModRefl_f_app]
  simp only [Functor.map_id]
  change 𝟙 ((emUnderlyingBar alg).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) ≫
    𝟙 ((emUnderlyingBar alg).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) =
    𝟙 ((emUnderlyingBar alg).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)))
  simp only [Category.id_comp]

/-- For a monad T on C, algebra morphism φ : alg → alg′, and simplex Δ, the Δ-component of
emLiteralHom(φ).left equals the Δ-component of resolutionHom(φ).left. Both are the map induced
by φ on the same underlying regular-right bar term. -/
private theorem emLiteralHom_app_eq_resolutionHom_app {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') (Δ : SimplexCategoryᵒᵖ) :
    (emLiteralHom φ).left.app Δ = (resolutionHom φ).left.app Δ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ]
  simp only [emLiteralHom_left, resolutionHom_left, algebraBarHom,
    Functor.whiskerRight_app, emEvalAlgebra_map_app,
    twoSidedBarHom_app_app, algebraLeftModuleHom_f_app]
  rfl

/-- Let T be a monad on C and φ : alg → alg′ an algebra morphism. The augmented isomorphism
e=emLiteralResolutionIso satisfies emLiteralHom(φ) ≫ e_alg′.hom = e_alg.hom ≫
resolutionHom(φ). This is naturality of the comparison on both simplicial and
augmentation-target components. -/
theorem emLiteralResolution_naturality {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') :
    emLiteralHom φ ≫ (emLiteralResolutionIso alg').hom =
      (emLiteralResolutionIso alg).hom ≫ resolutionHom φ := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have hAL : (emLiteralResolutionIso alg).hom.left =
        (emLiteralIso alg).hom.left ≫ (emAugmentedIso alg).hom.left := rfl
    have hAL' : (emLiteralResolutionIso alg').hom.left =
        (emLiteralIso alg').hom.left ≫ (emAugmentedIso alg').hom.left := rfl
    have hLitL : (emLiteralIso alg).hom.left = (emLiteralBarIso alg).hom := rfl
    have hLitL' : (emLiteralIso alg').hom.left =
        (emLiteralBarIso alg').hom := rfl
    rw [Comma.comp_left, Comma.comp_left, hAL, hAL', hLitL, hLitL',
      emAugmentedIso_hom_left,
      emAugmentedIso_hom_left]
    ext Δ
    have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
      obtain ⟨d⟩ := Δ
      exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
    rw [hΔ]
    simp only [← resolutionAugmented_left, ← emUnderlyingAugmented_left]
    rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
      NatTrans.comp_app]
    simp only [emLiteralBarIso_hom_app, emUnderlyingBarIso_hom_app_id,
      emLiteralHom_left, resolutionHom_left, algebraBarHom,
      Functor.whiskerRight_app]
    change (emLiteralHom φ).left.app Δ ≫
        𝟙 ((emLiteralAugmented alg').left.obj Δ) ≫
        𝟙 ((emUnderlyingBar alg').obj Δ) =
      (𝟙 ((emLiteralAugmented alg).left.obj Δ) ≫
        𝟙 ((emUnderlyingBar alg).obj Δ)) ≫
        (resolutionHom φ).left.app Δ
    change (emLiteralHom φ).left.app Δ ≫
        𝟙 ((emLiteralAugmented alg').left.obj Δ) ≫
        𝟙 ((emLiteralAugmented alg').left.obj Δ) =
      (𝟙 ((emLiteralAugmented alg).left.obj Δ) ≫
        𝟙 ((emLiteralAugmented alg).left.obj Δ)) ≫
        (resolutionHom φ).left.app Δ
    simp only [Category.comp_id]
    change (emLiteralHom φ).left.app Δ =
      𝟙 ((resolutionAugmented alg).left.obj Δ) ≫
        (resolutionHom φ).left.app Δ
    simp only [Category.id_comp]
    exact emLiteralHom_app_eq_resolutionHom_app φ _
  · rw [Comma.comp_right, Comma.comp_right, emLiteralHom_right,
      resolutionHom_right, emLiteralResolutionIso_hom_right alg,
      emLiteralResolutionIso_hom_right alg']
    exact (Category.comp_id _).trans (Category.id_comp _).symm

end LiteralComparison

/-- The literal EM-to-resolution comparison is identity on each degree carrier. -/
@[simp]
theorem emLiteralResolutionIso_hom_left_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (emLiteralResolutionIso alg).hom.left.app Δ = 𝟙 _ := by
  change (emLiteralBarIso alg).hom.app Δ ≫
    (emUnderlyingBarIso alg).hom.app Δ = 𝟙 _
  rw [emLiteralBarIso_hom_app, emUnderlyingBarIso_hom_app_id]
  change 𝟙 ((resolutionBar alg).obj Δ) ≫ 𝟙 ((resolutionBar alg).obj Δ) = 𝟙 _
  exact Category.id_comp _

section UnderlyingContraction

/-- The extra degeneracy of the actual evaluated-and-forgotten EM bar.

Transport the canonical regular resolution contraction through `emLiteralResolutionIso`.
The source of this structure is the literal augmentation obtained by evaluating the
algebra-valued bar and forgetting its algebra structure. -/
noncomputable def emExtra (alg : T.Algebra) :
    SimplicialObject.Augmented.ExtraDegeneracy (emLiteralAugmented alg) :=
  SimplicialObject.Augmented.ExtraDegeneracy.ofIso (emLiteralResolutionIso alg).symm
    (resolutionExtra alg)

/-- The actual EM augmentation section is the monad unit at the algebra carrier. -/
@[simp]
theorem emExtra_s' (alg : T.Algebra) : (emExtra alg).s' = T.η.app alg.A := by
  change (emLiteralResolutionIso alg).hom.right ≫ T.η.app alg.A ≫
    (emLiteralResolutionIso alg).inv.left.app
      (Opposite.op (SimplexCategory.mk 0)) = T.η.app alg.A
  rw [emLiteralResolutionIso_hom_right]
  change 𝟙 alg.A ≫ T.η.app alg.A ≫
    (emLiteralResolutionIso alg).inv.left.app (Opposite.op (SimplexCategory.mk 0)) =
      T.η.app alg.A
  rw [Category.id_comp]
  have hi := congrArg
    (fun f : emLiteralAugmented alg ⟶ emLiteralAugmented alg =>
      f.left.app (Opposite.op (SimplexCategory.mk 0)))
    (emLiteralResolutionIso alg).hom_inv_id
  change (emLiteralResolutionIso alg).hom.left.app
      (Opposite.op (SimplexCategory.mk 0)) ≫
    (emLiteralResolutionIso alg).inv.left.app
      (Opposite.op (SimplexCategory.mk 0)) = 𝟙 _ at hi
  rw [emLiteralResolutionIso_hom_left_app] at hi
  change 𝟙 (T.obj alg.A) ≫
    (emLiteralResolutionIso alg).inv.left.app (Opposite.op (SimplexCategory.mk 0)) =
      𝟙 (T.obj alg.A) at hi
  rw [Category.id_comp] at hi
  rw [hi, Category.comp_id]

/-- The transported section splits the actual forgotten EM augmentation. -/
noncomputable def emSplitEpi (alg : T.Algebra) :
    SplitEpi (emLiteralAugmented alg).hom :=
  (emExtra alg).splitEpi

/-- The transported contraction gives the canonical homotopy on the actual EM bar. -/
noncomputable def emHomotopy (alg : T.Algebra) :
    SimplicialObject.Homotopy
      ((emLiteralAugmented alg).hom ≫ (emExtra alg).section_)
      (𝟙 (emLiteralAugmented alg).left) :=
  (emExtra alg).homotopy

end UnderlyingContraction

end Monad
end CategoryTheory
