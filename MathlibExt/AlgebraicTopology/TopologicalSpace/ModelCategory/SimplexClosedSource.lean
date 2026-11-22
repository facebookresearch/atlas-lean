/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHGeneratorSourceSmallness
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
public import MathlibExt.CategoryTheory.Limits.Preserves.Retract
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Actual realized simplex sources along the original closed chains

The original simplex is a strict retract of an original positive-dimensional
horn through its zero coface and zero codegeneracy. Its native realization
keeps the actual comparison with the literal finite horn-generator source.
The established horn-source engine and functor-retract preservation then
give the actual simplex-source conclusion at the same realized-generator
cardinal. No model, source-Hom or small-object witness is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet

/-- The actual zero coface and codegeneracy exhibit Δ[n] as a strict horn retract. -/
@[no_expose]
def simplexHornRetract (n : ℕ) :
    Retract (Δ[n] : SSet.{v})
      (Λ[n + 1, (0 : Fin (n + 1)).succ] : SSet.{v}) where
  i := horn.ι (0 : Fin (n + 1)).succ (0 : Fin (n + 1)).castSucc
    (0 : Fin (n + 1)).castSucc_lt_succ.ne
  r := (Λ[n + 1, (0 : Fin (n + 1)).succ]).ι ≫
    stdSimplex.σ (0 : Fin (n + 1))
  retract := by
    rw [← Category.assoc, horn.ι_ι]
    exact CosimplicialObject.δ_comp_σ_self stdSimplex

/-- The actual section recovers the original zero coface after horn inclusion. -/
theorem simplexHornRetract_i_ι (n : ℕ) :
    (simplexHornRetract.{v} n).i ≫
        (Λ[n + 1, (0 : Fin (n + 1)).succ]).ι =
      stdSimplex.δ (0 : Fin (n + 1)).castSucc :=
  horn.ι_ι _ _ _

private theorem simplexHornRetract_r_private (n : ℕ) :
    (simplexHornRetract.{v} n).r =
      (Λ[n + 1, (0 : Fin (n + 1)).succ]).ι ≫
        stdSimplex.σ (0 : Fin (n + 1)) := rfl

/-- The original retraction is the horn inclusion followed by the zero codegeneracy. -/
theorem simplexHornRetract_r (n : ℕ) :
    (simplexHornRetract.{v} n).r =
      (Λ[n + 1, (0 : Fin (n + 1)).succ]).ι ≫
        stdSimplex.σ (0 : Fin (n + 1)) :=
  simplexHornRetract_r_private n

end SSet

namespace CGWH

/-- Realization preserves the strict retract with its larger endpoint normalized
to the literal native horn-generator source. -/
@[no_expose]
def realizedSimplexHornRetract (n : ℕ) :
    Retract (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v}))
      (SSet.toCGWHOfFinite (Λ[n + 1, (0 : Fin (n + 1)).succ] : SSet.{v})) := by
  let h := (SSet.simplexHornRetract.{v} n).map SSet.toCGWH.{u, v}
  let e : SSet.toCGWH.{u, v}.obj
      (Λ[n + 1, (0 : Fin (n + 1)).succ] : SSet.{v}) ≅
        SSet.toCGWHOfFinite (Λ[n + 1, (0 : Fin (n + 1)).succ] : SSet.{v}) :=
    finiteRealizationIso _
  exact
    { i := h.i ≫ e.hom
      r := e.inv ≫ h.r
      retract := by
        simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h.retract }

/-- The reflected native simplex source preserves the original closed-chain colimit. -/
theorem realizedSimplexSource_preservesClosedColimit
    (n : ℕ)
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ CGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (CGWH.cgwhToTop.map (F.map φ)).hom) :
    PreservesColimit F
      (coyoneda.obj (Opposite.op (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v})))) := by
  let h := realizedSimplexHornRetract.{u, v} n
  have hHorn : PreservesColimit F (coyoneda.obj (Opposite.op
      (SSet.toCGWHOfFinite (Λ[n + 1, (0 : Fin (n + 1)).succ] : SSet.{v})))) :=
    realizedGeneratorSource_preservesClosedColimit
      (realizedHornInclusion n (0 : Fin (n + 1)).succ)
      (Or.inr (horn_mem_realizedHornInclusions n _)) F hF
  let _ := hHorn
  exact Limits.preservesColimit_of_retract (K := F) (h.op.map coyoneda)

end CGWH

namespace PointedCGWH

/-- Costar preserves the actual strict simplex-to-native-horn source retract. -/
@[no_expose]
def realizedSimplexHornRetract (n : ℕ) :
    Retract
      ((Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v})))
      ((Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWHOfFinite (Λ[n + 1, (0 : Fin (n + 1)).succ] : SSet.{v}))) :=
  (CGWH.realizedSimplexHornRetract.{u, v} n).map (Under.costar CGWH.point)

/-- Freely pointed actual simplex sources preserve the same original closed-chain colimit. -/
theorem realizedSimplexSource_preservesClosedColimit
    (n : ℕ)
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (ConcreteCategory.hom (F.map φ).right)) :
    PreservesColimit F (coyoneda.obj (Opposite.op
      ((Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v}))))) := by
  let h := realizedSimplexHornRetract.{u, v} n
  let L := Under.costar CGWH.point.{u, v}
  let g := CGWH.realizedHornInclusion.{v, u} n (0 : Fin (n + 1)).succ
  have hHorn : PreservesColimit F (coyoneda.obj (Opposite.op
      (L.obj (SSet.toCGWHOfFinite
        (Λ[n + 1, (0 : Fin (n + 1)).succ] : SSet.{v}))))) :=
    PointedCGWH.realizedHornSource_preservesClosedColimit
      (L.map g) (MorphismProperty.strictMap.map
        (CGWH.horn_mem_realizedHornInclusions n _)) F hF
  let _ := hHorn
  exact Limits.preservesColimit_of_retract (K := F) (h.op.map coyoneda)

end PointedCGWH
