/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialIndexStabilizationArrowTransport
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.ShiftOmega
import MathlibExt.CategoryTheory.Enriched.SphereOperatorSourceNaturality

/-!
# Sequential index maps in orthogonal stabilization

The finite-bijection index functor into the orthogonal index preserves the supplied point
maps and braiding. Its degree-one successor permutation is identified with the prescribed
braiding and addition isomorphism. Mapping these index isomorphisms through the right-shift
diagram gives the original orthogonal operator maps.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Enriched CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.SpectrumIndexMaps
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalSequentialIndexSourceBridge

/-- The continuous isometry category used by the original orthogonal source. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original direct sum tensor on the continuous orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The pointed continuous enrichment of the original orthogonal index. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block symmetry of the continuous orthogonal index. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf

local notation "I" => Operad.SmallFinBijGroupoid
private abbrev R := PointedCGWH.copowerRestriction.{u, v, 0} I
private abbrev bareEnriched : EnrichedFunctor PointedCGWH.{u, v}
    (PointedCGWH.CopowerUnderlying.{u, v, 0} I) OrthogonalIndex :=
  symmetricOrthogonalIndexFunctor.{u, v}

/-- The actual finite-bijection-to-continuous-isometry functor, with all original index maps. -/
def bareIndexFunctor : I ⥤ OrthogonalIndex :=
  R.{u, v} ⋙ bareEnriched.{u, v}.toOrdinaryFunctor

/-- Its complete original map is the actual finite-bijection Hom generator. -/
theorem bareIndexFunctor_point {n k : I} (f : n ⟶ k) :
    eHomEquiv PointedCGWH.{u, v} (bareIndexFunctor.map f) =
      PointedCGWH.basedDiscreteIncl.{u, v, 0} (n ⟶ k) f ≫
        symmetricOrthogonalHomMap.{u, v} n k :=
  bareEnriched.toOrdinaryFunctor_map (R.map f)

private theorem bareEnriched_leftUnitor (n : I) :
    bareEnriched.{u, v}.toOrdinaryFunctor.map (λ_ (R.{u, v}.obj n)).hom =
      (λ_ (n.of.len : OrthogonalIndex)).hom := by
  apply (eHomEquiv PointedCGWH.{u, v}).injective
  exact (bareEnriched.toOrdinaryFunctor_map (λ_ (R.obj n)).hom).trans
    (symmetricOrthogonalLeftUnitor n)

/-- The original finite block braid maps to the same actual complete orthogonal block braid. -/
theorem bareIndexFunctor_braiding (a b : I) :
    bareIndexFunctor.{u, v}.map (β_ a b).hom =
      (β_ (a.of.len : OrthogonalIndex) b.of.len).hom := by
  apply (eHomEquiv PointedCGWH.{u, v}).injective
  exact (bareIndexFunctor_point (β_ a b).hom).trans
    ((symmetricOrthogonalHomMap_generator (β_ a b).hom).trans
      (congrArg (OrthogonalIndex.matrixPoint.{u, v}) (smallBijectionMatrix_braiding a b)))

/-- Both actual maps of the entire original block Iso are retained. -/
theorem bareIndexFunctor_braidingIso (a b : I) :
    bareIndexFunctor.{u, v}.mapIso (β_ a b) =
      (β_ (a.of.len : OrthogonalIndex) b.of.len) := by
  apply Iso.ext
  exact bareIndexFunctor_braiding a b

/-- Original unit coefficients and complete Hom generators commute with every native index point. -/
theorem symmetricIndexPoint_map {n k : I} (f : n ⟶ k) :
    symmetricIndexPoint.{u, v} n k f ≫ symmetricOrthogonalOperatorHomMap.{u, v} n k =
      eHomEquiv PointedCGWH.{u, v} (bareIndexFunctor.map f) ≫
        indexHom OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
          orthogonalSphereMonoidalData.{u, v} n.of.len k.of.len := by
  let ds := PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I
  let Ss := PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
  let Ls := PointedCGWH.sphereCopowerLaxData.{u, v}
  let do' := OrthogonalIndex.enrichedMonoidalData.{u, v}
  let So := orthogonalSphereFunctor.{u, v}
  let Lo := orthogonalSphereMonoidalData.{u, v}
  let U := 𝟙_ PointedCGWH.{u, v}
  let ps := eHomEquiv PointedCGWH.{u, v} ((λ_ (R.obj n)).hom ≫ R.map f)
  let po := eHomEquiv PointedCGWH.{u, v}
    ((λ_ (n.of.len : OrthogonalIndex)).hom ≫ bareIndexFunctor.map f)
  let q := symmetricOrthogonalHomMap.{u, v} ((𝟙_ I) ⊗ n) k
  let c := (originalSymmetricOrthogonalCoefficientIso.{u, v} (𝟙_ I)).hom
  let is := weightedCoend.ι (weight ds (R.obj n) (R.obj k)) Ss (R.obj (𝟙_ I))
  let io := OrthogonalOperatorIndex.ι.{u, v} n.of.len k.of.len 0
  let j := symmetricOrthogonalOperatorHomMap.{u, v} n k
  have hs : symmetricIndexPoint n k f = (λ_ U).inv ≫ (ps ⊗ₘ Ls.epsilon) ≫ is :=
    indexHom_point ds Ss Ls (R.map f)
  have ho : eHomEquiv PointedCGWH.{u, v} (bareIndexFunctor.map f) ≫
      indexHom do' So Lo n.of.len k.of.len = (λ_ U).inv ≫ (po ⊗ₘ Lo.epsilon) ≫ io :=
    indexHom_point do' So Lo (bareIndexFunctor.map f)
  have hp : ps ≫ q = po := by
    have h := bareEnriched.toOrdinaryFunctor_map ((λ_ (R.obj n)).hom ≫ R.map f)
    have hLabel : bareEnriched.toOrdinaryFunctor.map ((λ_ (R.obj n)).hom ≫ R.map f) =
        (λ_ (n.of.len : OrthogonalIndex)).hom ≫ bareIndexFunctor.map f := by
      rw [bareEnriched.toOrdinaryFunctor.map_comp, bareEnriched_leftUnitor]
      rfl
    exact h.symm.trans (congrArg (eHomEquiv PointedCGWH.{u, v}) hLabel)
  have he : Ls.epsilon ≫ c = Lo.epsilon := by
    have h := originalSymmetricOrthogonalCoefficientNatIso_unit.{u, v}
    rw [originalSymmetricOrthogonalCoefficientNatIso_hom_component] at h
    exact h
  have hg : is ≫ j = (q ⊗ₘ c) ≫ io :=
    symmetricOrthogonalOperatorHomMap_generator n k (𝟙_ I)
  have hPair : (ps ⊗ₘ Ls.epsilon) ≫ (q ⊗ₘ c) = po ⊗ₘ Lo.epsilon :=
    (tensorHom_comp_tensorHom ps Ls.epsilon q c).trans
      (congrArg₂ (fun p e => p ⊗ₘ e) hp he)
  have hPairIo : (ps ⊗ₘ Ls.epsilon) ≫ ((q ⊗ₘ c) ≫ io) =
      (po ⊗ₘ Lo.epsilon) ≫ io :=
    (Category.assoc (ps ⊗ₘ Ls.epsilon) (q ⊗ₘ c) io).symm.trans
      (congrArg (fun h => h ≫ io) hPair)
  have hGen := congrArg (fun h => (λ_ U).inv ≫ (ps ⊗ₘ Ls.epsilon) ≫ h) hg
  have hTail := congrArg (fun h => (λ_ U).inv ≫ h) hPairIo
  have hAssoc : ((λ_ U).inv ≫ (ps ⊗ₘ Ls.epsilon) ≫ is) ≫ j =
      (λ_ U).inv ≫ (ps ⊗ₘ Ls.epsilon) ≫ (is ≫ j) :=
    (Category.assoc (λ_ U).inv ((ps ⊗ₘ Ls.epsilon) ≫ is) j).trans
      (congrArg (fun h => (λ_ U).inv ≫ h) (Category.assoc (ps ⊗ₘ Ls.epsilon) is j))
  exact (congrArg (fun h => h ≫ j) hs).trans
    (hAssoc.trans (hGen.trans (hTail.trans ho.symm)))


/-- The original mapped successor permutation has both full actual isometry maps. -/
def bareSuccessorPermutation (n : ℕ) :
    (n + 1 : OrthogonalIndex) ≅ n + 1 :=
  bareIndexFunctor.mapIso (successorTargetPermutation n)

/-- Its entire original word is inverse block braid followed by the actual degree cast. -/
theorem bareSuccessorPermutation_word (n : ℕ) :
    bareSuccessorPermutation.{u, v} n =
      (β_ (1 : OrthogonalIndex) n).symm ≪≫ eqToIso (Nat.add_comm 1 n) := by
  change bareIndexFunctor.mapIso (successorTargetPermutation n) = _
  rw [successorTargetPermutation, Functor.mapIso_trans, Functor.mapIso_symm,
    bareIndexFunctor_braidingIso, eqToIso_map]
  rfl

/-- The full original beta and mapped successor cancel to the same actual coefficient-first cast. -/
theorem bareSuccessorPermutation_label (n : ℕ) :
    (β_ (1 : OrthogonalIndex) n).hom ≫ (bareSuccessorPermutation.{u, v} n).hom =
      eqToHom (Nat.add_comm 1 n) := by
  rw [bareSuccessorPermutation_word]
  exact Iso.hom_inv_id_assoc (β_ (1 : OrthogonalIndex) n) _

/-- Every original operator-index Iso has its genuine continuous source-index value map. -/
theorem mappedIndexIso_hom_value (X : FunctionSpectrum.RightShift.Carrier.{u, v})
    {n k : I} (e : n ≅ k) :
    indexMap X (symmetricOrthogonalOperatorIndexFunctor.forget.mapIso
      (symmetricIndexIso e)).hom =
        (FunctionSpectrum.RightShift.bare X).map (bareIndexFunctor.mapIso e).hom := by
  unfold indexMap
  change (eHomEquiv PointedCGWH.{u, v}).symm
    ((ForgetEnrichment.homTo PointedCGWH.{u, v} (symmetricIndexIso e).hom ≫
      symmetricOrthogonalOperatorHomMap n k) ≫
        X.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
          (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)) = _
  let z := X.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n.of.len)
    (OrthogonalOperatorIndex.ofIndex.{u, v} k.of.len)
  let i := indexHom OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v} n.of.len k.of.len
  let b := bareIndexFunctor.map e.hom
  have hStart := congrArg (fun p => (eHomEquiv PointedCGWH.{u, v}).symm
    ((p ≫ symmetricOrthogonalOperatorHomMap n k) ≫ z)) (symmetricIndexIso_hom e)
  have hPoint := congrArg (fun p => (eHomEquiv PointedCGWH.{u, v}).symm (p ≫ z))
    (symmetricIndexPoint_map e.hom)
  have hAssoc := congrArg (eHomEquiv PointedCGWH.{u, v}).symm
    (Category.assoc (eHomEquiv PointedCGWH.{u, v} b) i z)
  exact hStart.trans (hPoint.trans (hAssoc.trans rfl))


/-- The j successor uses that same whole original continuous target isometry, at every n. -/
theorem successorOrthogonalIndexIso_hom_value (X : FunctionSpectrum.RightShift.Carrier.{u, v})
    (n : ℕ) :
    indexMap X (successorOrthogonalIndexIso n).hom =
      (FunctionSpectrum.RightShift.bare X).map (bareSuccessorPermutation n).hom :=
  mappedIndexIso_hom_value X (successorTargetPermutation n)

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalSequentialIndexSourceBridge
