/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.CoreFibration
public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoEndpoint
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint

/-!
# Coherent endpoint lifting and strict equivalence lifting

For an inner fibration with quasicategory codomain, lifting against the
original source endpoint of the coherent walking-isomorphism nerve is
exactly strict lifting of the original equivalence edge. Source
quasicategory structure is inferred.

Both coherent-interval inclusions are proved Kan–Quillen anodyne using
actual nerve contractibility and the selected Kan–Quillen model. Maps from
the coherent interval factor through the literal core; the canonical core
fibration theorem lifts the whole prescribed base. Conversely its Kan core
extends the original equivalence edge to the coherent interval. Both the
original image edge and the prescribed target vertex are retained.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open HomotopicalAlgebra MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet

private lemma coherent_to_point_weak :
    SSet.realizationWeakEquivalences SSet.coherentIso.toDeltaZero.{u} := by
  let hT : IsTerminal (WalkingIso.zero.{u}) :=
    IsTerminal.ofUniqueHom (fun w => (Codiscrete.iso w WalkingIso.zero).hom)
      (fun _ _ => Subsingleton.elim _ _)
  exact NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isTerminal hT

private lemma coherent_endpoint_mono : Mono SSet.coherentIso.endpointInclusion.{u} := by
  constructor
  intro Z f g h
  have hh := congrArg (fun a => a ≫ SSet.coherentIso.toDeltaZero) h
  simpa only [Category.assoc, SSet.coherentIso.endpointInclusion_comp_toDeltaZero,
    Category.comp_id] using hh

private lemma coherent_endpoint_weak :
    SSet.realizationWeakEquivalences SSet.coherentIso.endpointInclusion.{u} := by
  apply SSet.realizationWeakEquivalences.of_postcomp
    SSet.coherentIso.endpointInclusion SSet.coherentIso.toDeltaZero coherent_to_point_weak
  rw [SSet.coherentIso.endpointInclusion_comp_toDeltaZero]
  exact SSet.realizationWeakEquivalences.id_mem _

private lemma mono_forward : Mono (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge :
    (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso.{u}) := by
  have hobj : Function.Injective SSet.coherentIso.hom.edge.obj := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have hh := congrArg WalkingIso.equivBool hij
      change false = true at hh
      cases hh
    · have hh := congrArg WalkingIso.equivBool hij
      change true = false at hh
      cases hh
    · rfl
  constructor
  intro Z f g h
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro z
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  have hk := congrArg (fun a => (a.app Δ z).obj k) h
  exact hobj hk

private lemma coherent_forward_weak :
    SSet.realizationWeakEquivalences (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge :
      (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso.{u}) := by
  have hN := NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_hasTerminal
    (C := ULift.{u} (Fin 2))
  have hΔ : SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) := by
    have h := SSet.realizationWeakEquivalences.comp_mem
      (SSet.stdSimplex.isoNerve.{u} 1).hom
      (SSet.stdSimplex.isTerminalObj₀.from (nerve (ULift.{u} (Fin 2))))
      (SSet.realizationWeakEquivalences.of_isIso _) hN
    rwa [show (SSet.stdSimplex.isoNerve.{u} 1).hom ≫
      SSet.stdSimplex.isTerminalObj₀.from (nerve (ULift.{u} (Fin 2))) =
      SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u}) from SSet.stdSimplex.ext₀] at h
  apply SSet.realizationWeakEquivalences.of_postcomp _ _ coherent_to_point_weak
  rwa [show (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge :
      (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso.{u}) ≫ SSet.coherentIso.toDeltaZero =
      SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u}) from SSet.stdSimplex.ext₀]

private lemma coherent_endpoint_anodyne :
    SSet.anodyneExtensions SSet.coherentIso.endpointInclusion.{u} := by
  let : Mono SSet.coherentIso.endpointInclusion.{u} := coherent_endpoint_mono
  let : Cofibration SSet.coherentIso.endpointInclusion.{u} :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  let : WeakEquivalence SSet.coherentIso.endpointInclusion.{u} :=
    (weakEquivalence_iff _).mpr coherent_endpoint_weak
  rw [SSet.anodyneExtensions_eq_trivialCofibrations]
  exact mem_trivialCofibrations _

private lemma coherent_forward_anodyne :
    SSet.anodyneExtensions (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge :
      (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso.{u}) := by
  let f := (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge :
    (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso.{u})
  let : Mono f := mono_forward
  let : Cofibration f := SSet.modelCategoryQuillen.cofibration_of_mono _
  let : WeakEquivalence f := (weakEquivalence_iff _).mpr coherent_forward_weak
  rw [SSet.anodyneExtensions_eq_trivialCofibrations]
  exact mem_trivialCofibrations _

private lemma coherent_core_eq_top : SSet.core SSet.coherentIso.{u} = ⊤ := by
  apply le_antisymm le_top
  intro Δ s _
  change s ∈ (SSet.core (nerve WalkingIso.{u})).obj (op ⦋Δ.unop.len⦌)
  apply (SSet.mem_core_nerve_iff_forall_map'_isIso s).mpr
  intro i j hij hjn
  rw [Codiscrete.eq_iso_hom (s.map' i j)]
  infer_instance

private lemma coherent_range_le_core {Y : SSet.{u}} (b : SSet.coherentIso.{u} ⟶ Y) :
    SSet.Subcomplex.range b ≤ SSet.core Y := by
  intro Δ s hs
  obtain ⟨x, rfl⟩ := hs
  apply SSet.core_le_preimage b
  rw [coherent_core_eq_top]
  trivial

private lemma coherent_endpoint_lifting_of_strict
    {X Y : SSet.{u}} (p : X ⟶ Y) [SSet.InnerFibration p] [SSet.Quasicategory Y]
    [SSet.HasStrictEquivalenceLifting p] :
    HasLiftingProperty SSet.coherentIso.endpointInclusion p := by
  constructor
  intro a b hab
  let ac : (Δ[0] : SSet.{u}) ⟶ (SSet.core X : SSet.{u}) :=
    SSet.yonedaEquiv.symm ⟨SSet.yonedaEquiv a, SSet.mem_core_obj_zero _⟩
  have hac : ac ≫ (SSet.core X).ι = a := by
    dsimp only [ac]
    rw [SSet.yonedaEquiv_symm_comp]
    exact SSet.yonedaEquiv.symm_apply_apply a
  let bc : SSet.coherentIso.{u} ⟶ (SSet.core Y : SSet.{u}) :=
    SSet.Subcomplex.lift b (coherent_range_le_core b)
  have hbc : bc ≫ (SSet.core Y).ι = b := SSet.Subcomplex.lift_ι _ _
  have hsq : ac ≫ SSet.core.map p = SSet.coherentIso.endpointInclusion ≫ bc := by
    apply (cancel_mono (SSet.core Y).ι).mp
    rw [Category.assoc, SSet.core.map_ι, ← Category.assoc, hac,
      Category.assoc, hbc]
    exact hab.w
  let : Fibration (SSet.core.map p) := SSet.fibration_core_map_of_hasStrictEquivalenceLifting p
  obtain ⟨l, hl, hr⟩ :=
    (SSet.anodyneExtensions.hasLeftLiftingProperty coherent_endpoint_anodyne
      (SSet.core.map p)).sq_hasLift (CommSq.mk hsq)
  refine ⟨l ≫ (SSet.core X).ι, ?_, ?_⟩
  · rw [← Category.assoc, hl, hac]
  · rw [Category.assoc, ← SSet.core.map_ι, ← Category.assoc, hr, hbc]

private lemma coherent_equivalence_extension {Y : SSet.{u}} [SSet.Quasicategory Y]
    {y₀ y₁ : Y _⦋0⦌} (g : SSet.Edge y₀ y₁) (hg : g.IsEquivalence) :
    ∃ t : SSet.coherentIso.{u} ⟶ Y,
      SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge ≫ t = SSet.yonedaEquiv.symm g.edge := by
  let gc : (Δ[1] : SSet.{u}) ⟶ (SSet.core Y : SSet.{u}) :=
    SSet.yonedaEquiv.symm ⟨g.edge, SSet.mem_core_obj_one_iff.mpr (hg.of_edge_eq rfl)⟩
  have hgc : gc ≫ (SSet.core Y).ι = SSet.yonedaEquiv.symm g.edge := by
    dsimp only [gc]
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨tc, htc⟩ := SSet.anodyneExtensions.exists_lift_of_isFibrant gc
    coherent_forward_anodyne
  refine ⟨tc ≫ (SSet.core Y).ι, ?_⟩
  rw [← Category.assoc, htc, hgc]

private lemma strict_of_coherent_endpoint_lifting
    {X Y : SSet.{u}} (p : X ⟶ Y) [SSet.Quasicategory Y]
    (hLP : HasLiftingProperty SSet.coherentIso.endpointInclusion p) :
    SSet.HasStrictEquivalenceLifting p := by
  constructor
  intro x₀ y₁ g hg
  obtain ⟨t, ht⟩ := coherent_equivalence_extension g hg
  have hendpoint : SSet.coherentIso.endpointInclusion.{u} =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge := by
    exact (SSet.Edge.δ_one_yonedaEquiv_symm SSet.coherentIso.hom).symm
  have hcompat : SSet.yonedaEquiv.symm x₀ ≫ p = SSet.coherentIso.endpointInclusion ≫ t := by
    rw [hendpoint, Category.assoc, ht, SSet.Edge.δ_one_yonedaEquiv_symm]
    rw [SSet.yonedaEquiv_symm_comp]
  let sq : CommSq (SSet.yonedaEquiv.symm x₀) SSet.coherentIso.endpointInclusion p t := ⟨hcompat⟩
  let : sq.HasLift := hLP.sq_hasLift sq
  let l : SSet.coherentIso.{u} ⟶ X := sq.lift
  let raw : X _⦋1⦌ := SSet.yonedaEquiv
    (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge ≫ l)
  have hsrc : X.δ 1 raw = x₀ := by
    dsimp only [raw]
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, ← hendpoint]
    change SSet.yonedaEquiv (SSet.coherentIso.endpointInclusion ≫ sq.lift) = x₀
    rw [sq.fac_left, Equiv.apply_symm_apply]
  let x₁ : X _⦋0⦌ := X.δ 0 raw
  let e : SSet.Edge x₀ x₁ := SSet.Edge.mk raw hsrc rfl
  have he : e.IsEquivalence := by
    apply (SSet.coherentIso.isEquivalence_hom_map l).of_edge_eq
    change l.app (op ⦋1⦌) SSet.coherentIso.hom.edge = raw
    dsimp only [raw]
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hmap : (e.map p).edge = g.edge := by
    change p.app (op ⦋1⦌) (SSet.yonedaEquiv
      (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge ≫ l)) = g.edge
    rw [← SSet.yonedaEquiv_comp, Category.assoc]
    change SSet.yonedaEquiv (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge ≫
      (sq.lift ≫ p)) = g.edge
    rw [sq.fac_right, ht, Equiv.apply_symm_apply]
  have htarget : p.app (op ⦋0⦌) x₁ = y₁ := by
    calc p.app (op ⦋0⦌) x₁ = Y.δ 0 (e.map p).edge := (e.map p).tgt_eq.symm
      _ = Y.δ 0 g.edge := by rw [hmap]
      _ = y₁ := g.tgt_eq
  exact ⟨x₁, htarget, e, he, hmap⟩

/-- For an inner fibration with quasicategory codomain, the chosen coherent
isomorphism endpoint lifts exactly when original equivalence edges lift strictly. -/
public theorem hasStrictEquivalenceLifting_iff_hasLiftingProperty_coherentIso_endpointInclusion
    {X Y : SSet.{u}} (p : X ⟶ Y) [SSet.InnerFibration p] [SSet.Quasicategory Y] :
    SSet.HasStrictEquivalenceLifting p ↔
        HasLiftingProperty SSet.coherentIso.endpointInclusion p := by
  constructor
  · intro h
    let : SSet.HasStrictEquivalenceLifting p := h
    exact coherent_endpoint_lifting_of_strict p
  · exact strict_of_coherent_endpoint_lifting p

end SSet
