/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentTerminalFlagCoefficient

/-!
# Actual endpoint-preserving outer maps of original full beads

The same ordinal operator acts on every complete path flag by its native
direct image. Both original endpoints and the original coherent Hom map
are retained explicitly.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.OuterOperator

open SimplicialEnrichment
open TerminalFlag

variable {n m k : ℕ}

/-- The original source endpoint equation at the coefficient universe. -/
theorem lifted_zero (f : ⦋n⦌ ⟶ ⦋m⦌)
    (hf : f.toOrderHom 0 = 0) :
    f.toOrderHom.uliftMap (ULift.up.{u} 0) =
      ULift.up.{u} (0 : Fin (m + 1)) :=
  ULift.ext hf

/-- The original target endpoint equation at the coefficient universe. -/
theorem lifted_last (f : ⦋n⦌ ⟶ ⦋m⦌)
    (hf : f.toOrderHom (Fin.last n) = Fin.last m) :
    f.toOrderHom.uliftMap (ULift.up.{u} (Fin.last n)) =
      ULift.up.{u} (Fin.last m) :=
  ULift.ext hf

/-- The native direct-image functor of the same original endpoint-preserving operator. -/
def functor (f : ⦋n⦌ ⟶ ⦋m⦌) (h₀ : f.toOrderHom 0 = 0)
    (h₁ : f.toOrderHom (Fin.last n) = Fin.last m) :
    SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 1)))
      (ULift.up.{u} (Fin.last n)) ⥤
    SimplicialThickening.Path (ULift.up.{u} (0 : Fin (m + 1)))
      (ULift.up.{u} (Fin.last m)) :=
  SimplicialThickening.functorMap f.toOrderHom.uliftMap
    (.mk (ULift.up.{u} 0)) (.mk (ULift.up.{u} (Fin.last n))) ⋙
      PathEndpointTransport.retarget (lifted_zero.{u} f h₀) (lifted_last.{u} f h₁)

/-- The whole same original outer coefficient map. -/
def map (f : ⦋n⦌ ⟶ ⦋m⦌) (h₀ : f.toOrderHom 0 = 0)
    (h₁ : f.toOrderHom (Fin.last n) = Fin.last m) :
    coefficientObject.{u} n ⟶ coefficientObject.{u} m :=
  nerveMap (functor f h₀ h₁)

/-- Every original target flag is precisely the image of its complete source flag. -/
theorem map_flags (f : ⦋n⦌ ⟶ ⦋m⦌) (h₀ : f.toOrderHom 0 = 0)
    (h₁ : f.toOrderHom (Fin.last n) = Fin.last m)
    {q : SimplexCategoryᵒᵖ} (p : (coefficientObject.{u} n).obj q)
    (t : Fin (q.unop.len + 1)) :
    (((map f h₀ h₁).app q p).obj t).I =
      f.toOrderHom.uliftMap '' (p.obj t).I := rfl

/-- The whole outer coefficient map is the same original coherent map with its endpoint equations. -/
theorem map_coherent (f : ⦋n⦌ ⟶ ⦋m⦌) (h₀ : f.toOrderHom 0 = 0)
    (h₁ : f.toOrderHom (Fin.last n) = Fin.last m) :
    map.{u} f h₀ h₁ =
      (coherentSimplexMap.{u} f).map (initial.{u} n) (terminal.{u} n) ≫
      eqToHom (congrArg₂
        (fun i j : coherentSimplex.{u} ⦋m⦌ => i ⟶[SSet.{u}] j)
        (congrArg SimplicialThickening.mk (lifted_zero.{u} f h₀))
        (congrArg SimplicialThickening.mk (lifted_last.{u} f h₁))) := by
  change nerveMap
      (SimplicialThickening.functorMap f.toOrderHom.uliftMap
        (.mk (ULift.up.{u} 0)) (.mk (ULift.up.{u} (Fin.last n)))) ≫
      nerveMap (PathEndpointTransport.retarget (lifted_zero.{u} f h₀)
        (lifted_last.{u} f h₁)) = _
  exact congrArg (fun g =>
    nerveMap (SimplicialThickening.functorMap f.toOrderHom.uliftMap
      (.mk (ULift.up.{u} 0)) (.mk (ULift.up.{u} (Fin.last n)))) ≫ g)
    (PathEndpointTransport.nerve_retarget (lifted_zero.{u} f h₀)
      (lifted_last.{u} f h₁))

private instance {J : Type u} [LinearOrder J] (i j : J)
    (a b : SimplicialThickening.Path i j) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The actual identity ordinal acts as the whole coefficient identity. -/
theorem map_id (n : ℕ) :
    map.{u} (𝟙 ⦋n⦌) rfl rfl = 𝟙 (coefficientObject.{u} n) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro p
  refine Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    exact Set.image_id _
  · intro i j f
    exact Subsingleton.elim _ _

/-- The complete original coefficient maps retain actual ordinal composition. -/
theorem map_comp (f : ⦋n⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋k⦌)
    (f₀ : f.toOrderHom 0 = 0) (f₁ : f.toOrderHom (Fin.last n) = Fin.last m)
    (g₀ : g.toOrderHom 0 = 0) (g₁ : g.toOrderHom (Fin.last m) = Fin.last k) :
    map.{u} (f ≫ g)
      ((congrArg g.toOrderHom f₀).trans g₀)
      ((congrArg g.toOrderHom f₁).trans g₁) =
      map f f₀ f₁ ≫ map g g₀ g₁ := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro p
  refine Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    exact (Set.image_image g.toOrderHom.uliftMap f.toOrderHom.uliftMap (p.obj t).I).symm
  · intro i j h
    exact Subsingleton.elim _ _

/-- Every original inner scalar operator follows the same whole outer coefficient map. -/
theorem map_inner (f : ⦋n⦌ ⟶ ⦋m⦌) (h₀ : f.toOrderHom 0 = 0)
    (h₁ : f.toOrderHom (Fin.last n) = Fin.last m)
    {q r : SimplexCategoryᵒᵖ} (a : q ⟶ r) (p : (coefficientObject.{u} n).obj q) :
    (coefficientObject.{u} m).map a ((map f h₀ h₁).app q p) =
      (map f h₀ h₁).app r ((coefficientObject.{u} n).map a p) :=
  ConcreteCategory.congr_hom ((map f h₀ h₁).naturality a).symm p

end CategoryTheory.CoherentRealization.OriginalBead.OuterOperator
