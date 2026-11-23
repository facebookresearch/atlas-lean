/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidal

/-!
# The original native realized interval and its coordinates

The interval is the literal native realization of Delta[1], with its two
original face maps, whole boundary and actual ordinary interval clock.
These are realization and tensor data; no model-category hypothesis or
selected path/comparison witness is supplied.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

universe u v

namespace CGWH

/-- The original native realization of the one-simplex. -/
public abbrev nativeInterval : CGWH.{u, v} := SSet.toCGWH.{u, v}.obj (Δ[1] : SSet.{v})

private def nativeZero_isTerminal :
    IsTerminal (SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v})) := by
  letI : Unique (SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v})) :=
    inferInstanceAs (Unique (SSet.toTop.obj (Δ[0] : SSet.{v})))
  exact IsTerminal.ofUniqueHom
    (fun X => ConcreteCategory.ofHom (ContinuousMap.const X default))
    (by
      intro X f
      apply ConcreteCategory.hom_ext
      intro x
      exact Subsingleton.elim _ _)

/-- The actual singleton realization is the selected native tensor unit. -/
public def nativeZeroTensorUnitIso :
    SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅ 𝟙_ CGWH.{u, v} :=
  nativeZero_isTerminal.{u, v}.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit

/-- The two original native interval endpoints; zero is the δ₁ face and
one is the δ₀ face, retaining the original path orientation. -/
public def nativeIntervalEndpoint (ε : Fin 2) : 𝟙_ CGWH.{u, v} ⟶ nativeInterval.{u, v} :=
  nativeZeroTensorUnitIso.{u, v}.inv ≫ SSet.toCGWH.{u, v}.map (SSet.stdSimplex.δ ε.rev)

/-- The ORIGINAL whole realized one-boundary inclusion. -/
public abbrev nativeIntervalBoundary :
    SSet.toCGWH.{u, v}.obj (∂Δ[1] : SSet.{v}) ⟶ nativeInterval.{u, v} :=
  SSet.toCGWH.{u, v}.map ((SSet.boundary.{v} 1).ι)

/-- The two original endpoint maps INTO the whole original boundary. -/
public abbrev nativeIntervalBoundaryEndpoint (ε : Fin 2) :
    𝟙_ CGWH.{u, v} ⟶ SSet.toCGWH.{u, v}.obj (∂Δ[1] : SSet.{v}) :=
  nativeZeroTensorUnitIso.{u, v}.inv ≫ SSet.toCGWH.{u, v}.map (SSet.boundary.ι ε.rev)

/-- The full endpoint factorization is the original boundary triangle. -/
private theorem nativeIntervalBoundaryEndpoint_comp_computed (ε : Fin 2) :
    nativeIntervalBoundaryEndpoint.{u, v} ε ≫ nativeIntervalBoundary.{u, v} =
      nativeIntervalEndpoint.{u, v} ε := by
  unfold nativeIntervalEndpoint
  change (nativeZeroTensorUnitIso.{u, v}.inv ≫ SSet.toCGWH.{u, v}.map (SSet.boundary.ι ε.rev)) ≫
    SSet.toCGWH.{u, v}.map ((SSet.boundary.{v} 1).ι) =
      nativeZeroTensorUnitIso.{u, v}.inv ≫ SSet.toCGWH.{u, v}.map (SSet.stdSimplex.δ ε.rev)
  rw [Category.assoc, ← Functor.map_comp, SSet.boundary.ι_ι]

/-- The actual original endpoint factors through the SAME original whole boundary. -/
@[reassoc]
public theorem nativeIntervalBoundaryEndpoint_comp (ε : Fin 2) :
    nativeIntervalBoundaryEndpoint.{u, v} ε ≫ nativeIntervalBoundary.{u, v} =
      nativeIntervalEndpoint.{u, v} ε := nativeIntervalBoundaryEndpoint_comp_computed.{u, v} ε

/-- The ordinary clock of the SAME realized one-simplex. -/
public def nativeIntervalClock : C(nativeInterval.{u, v}, unitInterval) :=
  (⟨TopCat.I.homeomorph.{v}, TopCat.I.homeomorph.{v}.continuous⟩ :
      C(TopCat.I.{v}, unitInterval)).comp SSet.stdSimplex.toTopObjIsoI.{v}.hom.hom

private theorem nativeIntervalClock_zero_computed (a : 𝟙_ CGWH.{u, v}) :
    nativeIntervalClock.{u, v} (nativeIntervalEndpoint.{u, v} 0 a) = 0 := by
  unfold nativeIntervalClock nativeIntervalEndpoint
  letI : Unique (SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v})) :=
    inferInstanceAs (Unique (SSet.toTop.obj (Δ[0] : SSet.{v})))
  change TopCat.I.homeomorph.{v} (SSet.stdSimplex.toTopObjIsoI.{v}.hom
    (SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) (nativeZeroTensorUnitIso.{u, v}.inv a))) = 0
  rw [Subsingleton.elim (nativeZeroTensorUnitIso.{u, v}.inv a)
    (default : SSet.toTop.obj (Δ[0] : SSet.{v}))]
  have he : SSet.stdSimplex.toTopObjIsoI.{v}.hom
      (SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 2)) default) = (0 : TopCat.I.{v}) :=
    (congrArg SSet.stdSimplex.toTopObjIsoI.{v}.hom SSet.toTopObjIsoI_inv_zero).symm.trans
      (SSet.stdSimplex.toTopObjIsoI.{v}.inv_hom_id_apply _)
  rw [he]
  rfl

private theorem nativeIntervalClock_one_computed (a : 𝟙_ CGWH.{u, v}) :
    nativeIntervalClock.{u, v} (nativeIntervalEndpoint.{u, v} 1 a) = 1 := by
  unfold nativeIntervalClock nativeIntervalEndpoint
  letI : Unique (SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v})) :=
    inferInstanceAs (Unique (SSet.toTop.obj (Δ[0] : SSet.{v})))
  change TopCat.I.homeomorph.{v} (SSet.stdSimplex.toTopObjIsoI.{v}.hom
    (SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) (nativeZeroTensorUnitIso.{u, v}.inv a))) = 1
  rw [Subsingleton.elim (nativeZeroTensorUnitIso.{u, v}.inv a)
    (default : SSet.toTop.obj (Δ[0] : SSet.{v}))]
  have he : SSet.stdSimplex.toTopObjIsoI.{v}.hom
      (SSet.toTop.map (SSet.stdSimplex.δ (0 : Fin 2)) default) = (1 : TopCat.I.{v}) :=
    (congrArg SSet.stdSimplex.toTopObjIsoI.{v}.hom SSet.toTopObjIsoI_inv_one).symm.trans
      (SSet.stdSimplex.toTopObjIsoI.{v}.inv_hom_id_apply _)
  rw [he]
  rfl

/-- The original source face has clock zero. -/
public theorem nativeIntervalClock_zero (a : 𝟙_ CGWH.{u, v}) :
    nativeIntervalClock.{u, v} (nativeIntervalEndpoint.{u, v} 0 a) = 0 :=
  nativeIntervalClock_zero_computed.{u, v} a

/-- The original target face has clock one. -/
public theorem nativeIntervalClock_one (a : 𝟙_ CGWH.{u, v}) :
    nativeIntervalClock.{u, v} (nativeIntervalEndpoint.{u, v} 1 a) = 1 :=
  nativeIntervalClock_one_computed.{u, v} a

/-- The actual original interval homeomorphism, through the canonical
native/ordinary realization Iso and the existing standard-simplex clock. -/
public abbrev nativeIntervalHomeomorph : nativeInterval.{u, v} ≃ₜ unitInterval :=
  (TopCat.homeoOfIso
    ((SSet.realizationToTopIso.{u, v}).app (Δ[1] : SSet.{v}) ≪≫
      SSet.stdSimplex.toTopObjIsoI.{v})).trans TopCat.I.homeomorph.{v}

private theorem nativeIntervalHomeomorph_symm_apply_computed (t : unitInterval) :
    nativeIntervalHomeomorph.{u, v}.symm t =
      SSet.stdSimplex.toTopObjIsoI.{v}.inv (TopCat.I.homeomorph.{v}.symm t) := rfl

/-- Its inverse has the exact original realized-simplex parameter value. -/
public theorem nativeIntervalHomeomorph_symm_apply (t : unitInterval) :
    nativeIntervalHomeomorph.{u, v}.symm t =
      SSet.stdSimplex.toTopObjIsoI.{v}.inv (TopCat.I.homeomorph.{v}.symm t) :=
  nativeIntervalHomeomorph_symm_apply_computed.{u, v} t

/-- The same ordinary clock and its actual inverse compose to identity. -/
public theorem nativeIntervalClock_symm_apply (t : unitInterval) :
    nativeIntervalClock.{u, v} (nativeIntervalHomeomorph.{u, v}.symm t) = t := by
  unfold nativeIntervalClock
  change nativeIntervalHomeomorph.{u, v} (nativeIntervalHomeomorph.{u, v}.symm t) = t
  exact nativeIntervalHomeomorph.{u, v}.apply_symm_apply t

/-- The actual public clock also has its original left inverse on EVERY
native interval point, without unfolding either exported coordinate map. -/
public theorem nativeIntervalHomeomorph_symm_clock (s : nativeInterval.{u, v}) :
    nativeIntervalHomeomorph.{u, v}.symm (nativeIntervalClock.{u, v} s) = s := by
  have hc := nativeIntervalClock_symm_apply.{u, v} (nativeIntervalHomeomorph.{u, v} s)
  have hc' : nativeIntervalClock.{u, v} s = nativeIntervalHomeomorph.{u, v} s :=
    (congrArg nativeIntervalClock.{u, v}
      (nativeIntervalHomeomorph.{u, v}.symm_apply_apply s).symm).trans hc
  exact (congrArg nativeIntervalHomeomorph.{u, v}.symm hc').trans
    (nativeIntervalHomeomorph.{u, v}.symm_apply_apply s)

/-- The original zero face is the original inverse-clock value zero. -/
public theorem nativeIntervalEndpoint_zero_apply (a : 𝟙_ CGWH.{u, v}) :
    nativeIntervalEndpoint.{u, v} 0 a = nativeIntervalHomeomorph.{u, v}.symm 0 := by
  have h := nativeIntervalHomeomorph_symm_clock.{u, v} (nativeIntervalEndpoint.{u, v} 0 a)
  rw [nativeIntervalClock_zero.{u, v}] at h
  exact h.symm

/-- The original one face is the original inverse-clock value one. -/
public theorem nativeIntervalEndpoint_one_apply (a : 𝟙_ CGWH.{u, v}) :
    nativeIntervalEndpoint.{u, v} 1 a = nativeIntervalHomeomorph.{u, v}.symm 1 := by
  have h := nativeIntervalHomeomorph_symm_clock.{u, v} (nativeIntervalEndpoint.{u, v} 1 a)
  rw [nativeIntervalClock_one.{u, v}] at h
  exact h.symm

end CGWH

end
