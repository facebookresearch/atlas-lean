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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalEquiv

/-!
# Normal actions on the actual predual

The action maps into the group of bundled normal star equivalences. Their
derived inverse pullbacks act on the actual closed normal-functional space.
Connes's source continuity condition is norm continuity of these actual
predual orbits, with their original continuous-dual norm and evaluation.

The primal star maps and all algebra values retain their original carriers.
The point sigma-strong-star source formulation keeps its comparison theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

noncomputable section

universe uG uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An actual normal automorphism action with Connes's norm-continuous predual inverse orbits. -/
structure NormalAction (G : Type uG) [Group G] [TopologicalSpace G]
    (M : VonNeumannAlgebra H) where
  /-- The actual action in the group of original bundled normal star equivalences. -/
  toMonoidHom : G →* NormalStarAlgEquiv M M
  /-- Norm continuity of every inverse orbit in the actual normal-functional subtype. -/
  continuous_predual_orbit : ∀ φ : normalFunctionalSpace M,
    Continuous fun g : G => NormalStarAlgEquiv.predualActionHom M (toMonoidHom g) φ

namespace NormalAction

variable {G : Type uG} [Group G] [TopologicalSpace G] {M : VonNeumannAlgebra H}

/-- The actual normal automorphism group homomorphism determines the action. -/
@[ext]
theorem ext {α β : NormalAction G M} (h : α.toMonoidHom = β.toMonoidHom) : α = β := by
  cases α
  cases β
  cases h
  rfl

@[macro_inline]
instance : FunLike (NormalAction G M) G (NormalStarAlgEquiv M M) where
  coe α := α.toMonoidHom
  coe_injective α β h := by
    have hmap : α.toMonoidHom = β.toMonoidHom :=
      DFunLike.ext _ _ fun g => congrFun h g
    exact ext hmap

instance : MonoidHomClass (NormalAction G M) G (NormalStarAlgEquiv M M) where
  map_one α := α.toMonoidHom.map_one
  map_mul α := α.toMonoidHom.map_mul

/-- The action map and original normal automorphism have the same value. -/
@[simp]
theorem toMonoidHom_apply (α : NormalAction G M) (g : G) : α.toMonoidHom g = α g :=
  rfl

/-- The original star automorphism action obtained by forgetting the proved normal data. -/
def toStarAlgAutHom (α : NormalAction G M) : G →* (M ≃⋆ₐ[ℂ] M) :=
  (NormalStarAlgEquiv.toStarAlgAutHom M).comp α.toMonoidHom

/-- The original algebra action evaluates at the same original point. -/
@[simp]
theorem toStarAlgAutHom_apply (α : NormalAction G M) (g : G) (x : M) :
    α.toStarAlgAutHom g x = α g x :=
  rfl

/-- Each action value has its actual ultraweak continuity from the normal equivalence bundle. -/
theorem continuous_ultraweak (α : NormalAction G M) (g : G) :
    Continuous fun x : Ultraweak M =>
      (ultraweakLinearEquiv M).symm (α g (ultraweakLinearEquiv M x)) :=
  (α g).continuous_ultraweak

/-- The induced covariant action on the actual predual, derived from inverse functional pullback. -/
def predualAction (α : NormalAction G M) :
    G →* (normalFunctionalSpace M ≃L[ℂ] normalFunctionalSpace M) :=
  (NormalStarAlgEquiv.predualActionHom M).comp α.toMonoidHom

/-- The actual predual action uses Connes's exact original inverse-automorphism evaluation. -/
@[simp]
theorem predualAction_apply (α : NormalAction G M) (g : G)
    (φ : normalFunctionalSpace M) (x : M) :
    (α.predualAction g φ : StrongDual ℂ M) x = (φ : StrongDual ℂ M) ((α g).symm x) :=
  NormalStarAlgEquiv.predualActionHom_apply (α g) φ x

/-- Every orbit is norm continuous in the actual original predual subtype. -/
theorem predualAction_continuous (α : NormalAction G M) (φ : normalFunctionalSpace M) :
    Continuous fun g : G => α.predualAction g φ :=
  α.continuous_predual_orbit φ

end NormalAction

end

end VonNeumannAlgebra
