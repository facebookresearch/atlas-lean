/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.MonicWeakInvariantEnlargement
import MathlibExt.AlgebraicTopology.SimplicialSpace.BoundedWeakRepresentatives
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyBoundaryCardinality
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyBoundaryFactorization
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyWeakEquivalences

/-!
# Strict bounded interpolation of Reedy boundary squares

Factor an arbitrary Rezk weak arrow in the already named Reedy model and lift
each literal boundary square against its true trivial-fibration factor. The
whole lifted boundary-codomain image is uniformly γ-small, so the prescribed
AF692 invariant enlargement applies to the monic weak left factor. Its literal
pullback yields a bounded Rezk weak intermediate arrow and a strict
factorization of the supplied whole Arrow morphism.

For a fixed literal boundary, pairing every bounded weak representative with
every incoming Arrow morphism gives a Type-u family. Every original square to
every Rezk weak arrow, without a monicity or endpoint-fibrancy premise,
strictly factors through this family with both components unchanged.
-/

set_option autoImplicit false
noncomputable section
open Cardinal CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped Simplicial
universe u

namespace SimplicialSpace
open ReedyGeneratingFamilies

variable {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]

/-- The full canonical-presheaf range of a map from a literal boundary target
fits inside the stable envelope bound. -/
theorem LocalReplacementCardinalEnvelope.boundaryRange_points_le
    (e : LocalReplacementCardinalEnvelope κ)
    (b : BoundaryIndex) {Z : SimplicialSpace.{u}}
    (l : (boundaryFamily.{u} b).right ⟶ Z) :
    Cardinal.mk
      (Subfunctor.range (toPresheaf.map l)).toFunctor.Elements ≤ e.γ := by
  calc
    _ ≤ Cardinal.mk (toPresheaf.obj (boundaryFamily.{u} b).right).Elements :=
      Subfunctor.mk_elements_range_le (toPresheaf.map l)
    _ = Cardinal.mk
        (Functor.uncurry.obj (boundaryFamily.{u} b).right.diagram).Elements :=
      (mk_totalPoints_toPresheaf (boundaryFamily.{u} b).right).symm
    _ ≤ e.γ := (e.boundaryFamily_endpoint_points_le b).2

/-- A bounded weak arrow interpolating one literal boundary square. -/
structure BoundaryWeakInterpolation
    (e : LocalReplacementCardinalEnvelope κ) (b : BoundaryIndex)
    (f : Arrow SimplicialSpace.{u})
    (sq : boundaryFamily.{u} b ⟶ f) where
  /-- The bounded Rezk weak intermediate arrow. -/
  q : Arrow SimplicialSpace.{u}
  /-- Both endpoint bounds and original Rezk weakness. -/
  q_bounded_weak : boundedRezkWeakArrows e.γ q
  /-- The incoming literal boundary square. -/
  incoming : boundaryFamily.{u} b ⟶ q
  /-- The outgoing square to the original weak arrow. -/
  outgoing : q ⟶ f
  /-- Strict whole-Arrow factorization of the supplied square. -/
  fac : incoming ≫ outgoing = sq

/-- Every square from a literal Reedy boundary to an arbitrary Rezk weak arrow
strictly factors through one bounded Rezk weak arrow. -/
theorem LocalReplacementCardinalEnvelope.exists_boundaryWeakInterpolation
    (e : LocalReplacementCardinalEnvelope κ) (b : BoundaryIndex)
    (f : Arrow SimplicialSpace.{u}) (hf : rezkWeakEquivalences f.hom)
    (sq : boundaryFamily.{u} b ⟶ f) :
    Nonempty (BoundaryWeakInterpolation e b f sq) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let d := ReedyGeneratingFamilies.monoFactorizationData f.hom
  have hpTrivial : trivialFibrations SimplicialSpace.{u} d.p := by
    rw [← I_rlp_eq_trivialFibrations]
    exact d.hp
  have hpReedy : weakEquivalences SimplicialSpace.{u} d.p := hpTrivial.2
  have hpWeak : rezkWeakEquivalences d.p :=
    reedyWeak_le_rezkWeak d.p hpReedy
  have hiWeak : rezkWeakEquivalences d.i :=
    rezkWeakEquivalences.of_postcomp d.i d.p hpWeak (by rwa [d.fac])
  have hlift : HasLiftingProperty (boundaryFamily.{u} b).hom d.p :=
    ReedyGeneratingFamilies.boundary_hasLiftingProperty b d.hp
  let liftSq : CommSq (sq.left ≫ d.i) (boundaryFamily.{u} b).hom d.p sq.right :=
    ⟨by rw [Category.assoc, d.fac]; exact sq.w⟩
  let l := liftSq.lift
  let U := Subfunctor.range (toPresheaf.map l)
  have hU : Cardinal.mk U.toFunctor.Elements ≤ e.γ :=
    e.boundaryRange_points_le b l
  obtain ⟨A⟩ := e.exists_monicWeakInvariantEnlargement d.i hiWeak U hU
  let V := A.invariant.V
  let j := originalSubpresheafInclusion V
  let k := pullback.snd d.i j
  let lV := originalSubpresheafLift l V A.invariant.le
  have hlV : lV ≫ j = l :=
    originalSubpresheafLift_inclusion l V A.invariant.le
  have comm : sq.left ≫ d.i = ((boundaryFamily.{u} b).hom ≫ lV) ≫ j := by
    rw [Category.assoc, hlV]
    exact liftSq.fac_left.symm
  let aV := pullback.lift sq.left ((boundaryFamily.{u} b).hom ≫ lV) comm
  let incoming : boundaryFamily.{u} b ⟶ Arrow.mk k :=
    Arrow.homMk aV lV (pullback.lift_snd ..)
  let outgoing : Arrow.mk k ⟶ f :=
    Arrow.homMk (pullback.fst d.i j) (j ≫ d.p) (by
      calc
        pullback.fst d.i j ≫ f.hom =
            pullback.fst d.i j ≫ (d.i ≫ d.p) :=
          congrArg (fun z => pullback.fst d.i j ≫ z) d.fac.symm
        _ = (pullback.fst d.i j ≫ d.i) ≫ d.p := (Category.assoc ..).symm
        _ = (pullback.snd d.i j ≫ j) ≫ d.p :=
          congrArg (fun z => z ≫ d.p) (pullback.condition (f := d.i) (g := j))
        _ = k ≫ (j ≫ d.p) := Category.assoc ..)
  have hfac : incoming ≫ outgoing = sq := by
    apply Arrow.hom_ext
    · change aV ≫ pullback.fst d.i j = sq.left
      exact pullback.lift_fst ..
    · change lV ≫ (j ≫ d.p) = sq.right
      rw [← Category.assoc, hlV]
      exact liftSq.fac_right
  exact ⟨{
    q := Arrow.mk k
    q_bounded_weak := ⟨A.pullback_raw_points_le,
      A.invariant.raw_points_le, A.projection_weak⟩
    incoming := incoming
    outgoing := outgoing
    fac := hfac }⟩

/-- Every literal Reedy boundary has a Type-u weakly initial family in its
comma category with all original Rezk weak arrows; each family object retains
both endpoint bounds by the same envelope cardinal. -/
theorem LocalReplacementCardinalEnvelope.boundedBoundaryWeakSolutionFamily
    (e : LocalReplacementCardinalEnvelope κ)
    {A B : SimplicialSpace.{u}} (i : A ⟶ B) (hi : I.{u} i) :
    ∃ (S : Type u)
      (q : S → rezkWeakEquivalences.{u}.arrowObjectProperty.FullSubcategory)
      (h : ∀ s, Arrow.mk i ⟶
        rezkWeakEquivalences.{u}.arrowObjectProperty.ι.obj (q s)),
      (∀ s, boundedRezkWeakArrows e.γ
        (rezkWeakEquivalences.{u}.arrowObjectProperty.ι.obj (q s))) ∧
        ∀ (T : rezkWeakEquivalences.{u}.arrowObjectProperty.FullSubcategory)
          (sq : Arrow.mk i ⟶
            rezkWeakEquivalences.{u}.arrowObjectProperty.ι.obj T),
          ∃ (s : S) (ψ : q s ⟶ T),
            h s ≫ rezkWeakEquivalences.{u}.arrowObjectProperty.ι.map ψ = sq := by
  classical
  obtain ⟨Γ, r, hr, hrep⟩ :=
    exists_boundedRezkWeakArrow_representatives e.γ
  let S : Type u := Σ γ : Γ, (Arrow.mk i ⟶ r γ)
  let q : S → rezkWeakEquivalences.{u}.arrowObjectProperty.FullSubcategory :=
    fun s => ⟨r s.1, (hr s.1).2.2⟩
  let h (s : S) : Arrow.mk i ⟶
      rezkWeakEquivalences.{u}.arrowObjectProperty.ι.obj (q s) := s.2
  refine ⟨S, q, h, fun s => hr s.1, ?_⟩
  intro T sq
  change MorphismProperty.ofHoms
    (fun b : BoundaryIndex => (boundaryFamily.{u} b).hom) i at hi
  obtain ⟨b, hI⟩ := (MorphismProperty.ofHoms_iff _ i).mp hi
  let eI : Arrow.mk i ≅ boundaryFamily.{u} b := eqToIso hI
  obtain ⟨D⟩ := e.exists_boundaryWeakInterpolation b T.obj T.property (eI.inv ≫ sq)
  obtain ⟨γ, ⟨E⟩⟩ := hrep D.q D.q_bounded_weak
  let s : S := ⟨γ, (eI.hom ≫ D.incoming) ≫ E.hom⟩
  let ψ : q s ⟶ T := ObjectProperty.homMk (E.inv ≫ D.outgoing)
  refine ⟨s, ψ, ?_⟩
  change ((eI.hom ≫ D.incoming) ≫ E.hom) ≫
      (E.inv ≫ D.outgoing) = sq
  calc
    _ = eI.hom ≫ (D.incoming ≫ D.outgoing) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = eI.hom ≫ (eI.inv ≫ sq) := by rw [D.fac]
    _ = sq := by simp only [Iso.hom_inv_id_assoc]

end SimplicialSpace
