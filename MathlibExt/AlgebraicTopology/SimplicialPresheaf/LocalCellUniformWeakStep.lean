/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalArrowImageEnvelope
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellReplacementSupport
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellWeakDetector
import Mathlib.CategoryTheory.Presentable.Basic

/-!
# A strict uniform original local weak step

One larger regular cardinal is chosen before the ambient arrow and seed.
The weak interpolation arrow is an actual subdiagram of the same replacement,
and both endpoint refinements make its two replacement maps commute strictly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits Cardinal
open SimplicialPresheaf.KanWeakInterpolation

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

private theorem uniformWeakInterpolation
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ lower : Cardinal.{u}) :
    ∃ (ν : Cardinal.{u}) (hν : Fact ν.IsRegular),
      letI : Fact ν.IsRegular := hν
      lower < ν ∧ μ < ν ∧ (originalLocalCellData S).κ < ν ∧
        ∀ a : Arrow (SimplicialPresheaf.{u} D), originalArrowPointBound μ a →
          (HasCardinalLT (originalTotalPoints ((originalLocalCellReplacement S).obj a.left)) ν ∧
            HasCardinalLT (originalTotalPoints ((originalLocalCellReplacement S).obj a.right)) ν ∧
            IsCardinalPresentable ((originalLocalCellReplacement S).obj a.left) ν ∧
            IsCardinalPresentable ((originalLocalCellReplacement S).obj a.right) ν) ∧
          ∀ {U V : SimplicialPresheaf.{u} D} (g : U ⟶ V),
            SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ g →
            ∀ α : (originalLocalCellReplacement S).mapArrow.obj a ⟶ Arrow.mk g,
              ∃ (b : Subdiagram g)
                (p : (originalLocalCellReplacement S).mapArrow.obj a ⟶
                  Subdiagram.arrow g b),
                SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ
                    (Subdiagram.hom g b) ∧
                  HasCardinalLT (originalTotalPoints (Subdiagram.arrow g b).left) ν ∧
                  HasCardinalLT (originalTotalPoints (Subdiagram.arrow g b).right) ν ∧
                  IsCardinalPresentable (Subdiagram.arrow g b).left ν ∧
                  IsCardinalPresentable (Subdiagram.arrow g b).right ν ∧
                  p ≫ Subdiagram.inclusion g b = α := by
  let R := originalLocalCellReplacement S
  obtain ⟨ν₀, hν₀, hLower₀, hμ₀, hκ₀, hImages⟩ :=
    exists_originalLocalCellImageEnvelope S μ lower
  let : Fact ν₀.IsRegular := hν₀
  obtain ⟨J, K, _hK, hcover⟩ := exists_originalArrowPointBound_representatives (D := D) μ
  choose γ L F incoming hFamily hFactor using
    (fun j : J => objectwiseKanWeakArrowInterpolation (R.mapArrow.obj (K j)))
  let Labels := Σ j : J, L j
  let H : Labels → Arrow (SimplicialPresheaf.{u} D) := fun l => F l.1 l.2
  let Fixed := Σ l : Labels, originalTotalPoints (H l).left ⊕ originalTotalPoints (H l).right
  let : Small.{u} Fixed := by infer_instance
  obtain ⟨ν, hν, hν₀ν, _hΩ, _hLabels, hFixed, _hLP, hRanks⟩ :=
    exists_regular_cardinal_for_family H ν₀ Fixed
  let : Fact ν.IsRegular := hν
  have hPoints (l : Labels) :
      HasCardinalLT (originalTotalPoints (H l).left) ν ∧
        HasCardinalLT (originalTotalPoints (H l).right) ν :=
    ⟨hFixed.of_injective (fun x => (⟨l, Sum.inl x⟩ : Fixed))
        (sigma_mk_injective.comp Sum.inl_injective),
      hFixed.of_injective (fun x => (⟨l, Sum.inr x⟩ : Fixed))
        (sigma_mk_injective.comp Sum.inr_injective)⟩
  refine ⟨ν, hν, hLower₀.trans hν₀ν, hμ₀.trans hν₀ν, hκ₀.trans hν₀ν, ?_⟩
  intro a ha
  obtain ⟨hAL, hAR, hRankAL, hRankAR⟩ := hImages a ha
  let : IsCardinalPresentable (R.obj a.left) ν₀ := hRankAL
  let : IsCardinalPresentable (R.obj a.right) ν₀ := hRankAR
  refine ⟨⟨hAL.of_le hν₀ν.le, hAR.of_le hν₀ν.le,
    isCardinalPresentable_of_le (R.obj a.left) hν₀ν.le,
    isCardinalPresentable_of_le (R.obj a.right) hν₀ν.le⟩, ?_⟩
  intro U V g hWeak α
  obtain ⟨j, ⟨e⟩⟩ := hcover a ha
  let αG : R.mapArrow.obj (K j) ⟶ Arrow.mk g := R.mapArrow.map e.inv ≫ α
  obtain ⟨k, outgoing, b, eB, hB, hOut, hFull, _hLeft, _hRight⟩ :=
    hFactor j (Arrow.mk g) hWeak αG
  let b' : Subdiagram g := b
  let eB' : F j k ≅ Subdiagram.arrow g b' := eB
  have hOut' : outgoing = eB'.hom ≫ Subdiagram.inclusion g b' := hOut
  let p : R.mapArrow.obj a ⟶ Subdiagram.arrow g b' :=
    R.mapArrow.map e.hom ≫ incoming j k ≫ eB'.hom
  have hp : p ≫ Subdiagram.inclusion g b' = α := by
    dsimp only [p]
    rw [Category.assoc, Category.assoc, ← hOut', hFull]
    dsimp only [αG]
    rw [← Category.assoc, ← R.mapArrow.map_comp, e.hom_inv_id,
      R.mapArrow.map_id, Category.id_comp]
  let eL : (F j k).left ≅ (Subdiagram.arrow g b').left :=
    Arrow.leftFunc.mapIso eB'
  let eR : (F j k).right ≅ (Subdiagram.arrow g b').right :=
    Arrow.rightFunc.mapIso eB'
  let : IsCardinalPresentable (F j k).left ν := (hRanks ⟨j, k⟩).1
  let : IsCardinalPresentable (F j k).right ν := (hRanks ⟨j, k⟩).2
  exact ⟨b', p, hB.1,
    (hasCardinalLT_iff_of_equiv (originalTotalPointsEquivOfIso eL) ν).mp (hPoints ⟨j, k⟩).1,
    (hasCardinalLT_iff_of_equiv (originalTotalPointsEquivOfIso eR) ν).mp (hPoints ⟨j, k⟩).2,
    isCardinalPresentable_of_iso eL ν, isCardinalPresentable_of_iso eR ν, hp⟩

private theorem uniformWeakStep_profile
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (ν : Cardinal.{u})
    (h : (originalLocalCellData S).κ ≤ ν) :
    ℵ₀ < ν ∧ HasCardinalLT (cardinalSubarrowWidth D) ν := by
  let d := originalLocalCellData S
  let := d.regular
  let := d.orderBot
  rcases d.properties with ⟨hΩ, _, hD, hOp, hDelta, _⟩
  have hWidth : HasCardinalLT (cardinalSubarrowWidth D) d.κ :=
    (hasCardinalLT_sum_iff _ _ _ hΩ.le).mpr
      ⟨hD, (hasCardinalLT_sum_iff _ _ _ hΩ.le).mpr ⟨hOp, hDelta⟩⟩
  exact ⟨hΩ.trans_le h, hWidth.of_le h⟩

private theorem refineUniformTriangle
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (ν : Cardinal.{u}) [Fact ν.IsRegular]
    (hκ : (originalLocalCellData S).κ ≤ ν)
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
    (s : cardinalSubarrowIndex f ν) (B : Arrow (SimplicialPresheaf.{u} D))
    [IsCardinalPresentable ((originalLocalCellReplacement S).mapArrow.obj
      (Subdiagram.arrow f s.val)).left ν]
    [IsCardinalPresentable ((originalLocalCellReplacement S).mapArrow.obj
      (Subdiagram.arrow f s.val)).right ν]
    [IsCardinalPresentable B.left ν] [IsCardinalPresentable B.right ν]
    (p : (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val) ⟶ B)
    (β : B ⟶ (originalLocalCellReplacement S).mapArrow.obj (Arrow.mk f))
    (hp : p ≫ β = (originalLocalCellReplacement S).mapArrow.map
      (Subdiagram.inclusion f s.val)) :
    ∃ (t : cardinalSubarrowIndex f ν) (hst : s.val ≤ t.val)
      (q : B ⟶ (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f t.val)),
      p ≫ q = (originalLocalCellReplacement S).mapArrow.map (Subdiagram.map f hst) ∧
        q ≫ (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f t.val) =
          β := by
  let R := originalLocalCellReplacement S
  obtain ⟨T, q₀, hsT, hq₀, _hL₀, _hR₀, _hSq₀⟩ :=
    exists_originalLocalCellSupport_above S ν hκ B f β s
  obtain ⟨hΩ, hWidth⟩ := uniformWeakStep_profile S ν hκ
  let := cardinalSubarrowIndex_isCardinalFiltered f ν
  let A := cardinalSubarrowDiagram f ν
  let AR := A ⋙ R.mapArrow
  let c : Cocone AR := R.mapArrow.mapCocone (cardinalSubarrowCocone f ν)
  let FL := AR ⋙ Arrow.leftFunc
  let FR := AR ⋙ Arrow.rightFunc
  let cL : Cocone FL := Arrow.leftFunc.mapCocone c
  let cR : Cocone FR := Arrow.rightFunc.mapCocone c
  have hcL : IsColimit cL := originalLocalCellReplacementPreservesCocone S ν hκ _
    (cardinalSubarrowLeftIsColimit f ν hΩ hWidth)
  have hcR : IsColimit cR := originalLocalCellReplacementPreservesCocone S ν hκ _
    (cardinalSubarrowRightIsColimit f ν hΩ hWidth)
  let h : s ⟶ T := homOfLE hsT
  let m := AR.map h
  let pA : AR.obj s ⟶ B := p
  let qA : B ⟶ AR.obj T := q₀
  let βA : B ⟶ c.pt := β
  have hm : m ≫ c.ι.app T = c.ι.app s := by
    exact c.w h
  have hqA : qA ≫ c.ι.app T = βA := hq₀
  have hpA : pA ≫ βA = c.ι.app s := hp
  have hTwo : (pA ≫ qA) ≫ c.ι.app T = m ≫ c.ι.app T := by
    rw [Category.assoc, hqA, hpA, hm]
  let aL : FL.obj s ⟶ FL.obj T := (pA ≫ qA).left
  let aR : FR.obj s ⟶ FR.obj T := (pA ≫ qA).right
  let mL : FL.obj s ⟶ FL.obj T := m.left
  let mR : FR.obj s ⟶ FR.obj T := m.right
  let : IsCardinalPresentable (FL.obj s) ν :=
    (inferInstance : IsCardinalPresentable (R.mapArrow.obj (Subdiagram.arrow f s.val)).left ν)
  let : IsCardinalPresentable (FR.obj s) ν :=
    (inferInstance : IsCardinalPresentable (R.mapArrow.obj (Subdiagram.arrow f s.val)).right ν)
  have hL : aL ≫ cL.ι.app T = mL ≫ cL.ι.app T :=
    congrArg Arrow.Hom.left hTwo
  have hR : aR ≫ cR.ι.app T = mR ≫ cR.ι.app T :=
    congrArg Arrow.Hom.right hTwo
  obtain ⟨TL, uL, hEqL⟩ := IsCardinalPresentable.exists_eq_of_isColimit' ν hcL
    aL mL hL
  obtain ⟨TR, uR, hEqR⟩ := IsCardinalPresentable.exists_eq_of_isColimit' ν hcR
    aR mR hR
  let family : Fin 2 → cardinalSubarrowIndex f ν := fun n => if n = 0 then TL else TR
  have hFinite : HasCardinalLT (Fin 2) ν := hasCardinalLT_of_finite _ _ hΩ.le
  let U := cardinalSubarrowUnion f ν family hFinite
  have hTLU : TL ≤ U := by
    simpa only [family, ite_eq_left rfl] using
      le_cardinalSubarrowUnion f ν family hFinite 0
  have hTRU : TR ≤ U := by
    simpa only [family, ite_eq_right (one_ne_zero : (1 : Fin 2) ≠ 0)] using
      le_cardinalSubarrowUnion f ν family hFinite 1
  let vL : TL ⟶ U := homOfLE hTLU
  let vR : TR ⟶ U := homOfLE hTRU
  let w : T ⟶ U := uL ≫ vL
  have hwR : uR ≫ vR = w := Subsingleton.elim _ _
  have hEqLU : aL ≫ FL.map w = mL ≫ FL.map w := by
    dsimp only [w]
    rw [FL.map_comp, ← Category.assoc, hEqL, Category.assoc]
  have hEqRU : aR ≫ FR.map w = mR ≫ FR.map w := by
    rw [← hwR, FR.map_comp, ← Category.assoc, hEqR, Category.assoc]
  have hAR : (pA ≫ qA) ≫ AR.map w = m ≫ AR.map w := by
    apply Arrow.hom_ext
    · exact hEqLU
    · exact hEqRU
  let q : B ⟶ AR.obj U := qA ≫ AR.map w
  have hsU : s.val ≤ U.val := leOfHom (h ≫ w)
  have hthin : h ≫ w = homOfLE (show s ≤ U from hsU) := Subsingleton.elim _ _
  have hwhole : pA ≫ q = R.mapArrow.map (Subdiagram.map f hsU) := by
    change pA ≫ (qA ≫ AR.map w) = AR.map (homOfLE (show s ≤ U from hsU))
    rw [← Category.assoc, hAR]
    change AR.map h ≫ AR.map w = AR.map (homOfLE (show s ≤ U from hsU))
    rw [← AR.map_comp, hthin]
  have hwholeAmbient : q ≫ c.ι.app U = βA := by
    have hNat : AR.map w ≫ c.ι.app U = c.ι.app T := by
      exact c.w w
    change (qA ≫ AR.map w) ≫ c.ι.app U = βA
    rw [Category.assoc, hNat, hqA]
  exact ⟨U, hsU, q, hwhole, hwholeAmbient⟩

/-- One larger regular budget, chosen before the ambient arrow and seed,
gives an actual weak subdiagram and both strict replacement-factor maps. -/
theorem exists_originalLocalUniformWeakStep
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (μ lower : Cardinal.{u}) :
    ∃ (ν : Cardinal.{u}) (hν : Fact ν.IsRegular),
      letI : Fact ν.IsRegular := hν
      lower < ν ∧ μ < ν ∧ (originalLocalCellData S).κ < ν ∧
        ∀ {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y),
          originalLocalEquivalences S f → ∀ s : cardinalSubarrowIndex f μ,
          ∃ (b : Subdiagram ((originalLocalCellReplacement S).map f))
            (t : cardinalSubarrowIndex f ν) (hst : s.val ≤ t.val)
            (p : (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val) ⟶
              Subdiagram.arrow ((originalLocalCellReplacement S).map f) b)
            (q : Subdiagram.arrow ((originalLocalCellReplacement S).map f) b ⟶
              (originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f t.val)),
            SSet.realizationWeakEquivalences.functorCategory Dᵒᵖ
                (Subdiagram.hom ((originalLocalCellReplacement S).map f) b) ∧
              HasCardinalLT (originalTotalPoints
                (Subdiagram.arrow ((originalLocalCellReplacement S).map f) b).left) ν ∧
              HasCardinalLT (originalTotalPoints
                (Subdiagram.arrow ((originalLocalCellReplacement S).map f) b).right) ν ∧
              IsCardinalPresentable
                (Subdiagram.arrow ((originalLocalCellReplacement S).map f) b).left ν ∧
              IsCardinalPresentable
                (Subdiagram.arrow ((originalLocalCellReplacement S).map f) b).right ν ∧
              HasCardinalLT (originalTotalPoints
                ((originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val)).left) ν ∧
              HasCardinalLT (originalTotalPoints
                ((originalLocalCellReplacement S).mapArrow.obj
                    (Subdiagram.arrow f s.val)).right) ν ∧
              IsCardinalPresentable
                ((originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val)).left ν ∧
              IsCardinalPresentable
                ((originalLocalCellReplacement S).mapArrow.obj (Subdiagram.arrow f s.val)).right ν ∧
              p ≫ q = (originalLocalCellReplacement S).mapArrow.map (Subdiagram.map f hst) ∧
              p ≫ Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b =
                (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f s.val) ∧
              q ≫ (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f t.val) =
                Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b ∧
              p.left ≫ q.left =
                (originalLocalCellReplacement S).map (Subdiagram.map f hst).left ∧
              p.right ≫ q.right =
                (originalLocalCellReplacement S).map (Subdiagram.map f hst).right ∧
              p.left ≫ (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).left =
                (originalLocalCellReplacement S).map (Subdiagram.leftInclusion f s.val) ∧
              p.right ≫ (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).right =
                (originalLocalCellReplacement S).map (Subdiagram.rightInclusion f s.val) ∧
              q.left ≫ (originalLocalCellReplacement S).map (Subdiagram.leftInclusion f t.val) =
                (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).left ∧
              q.right ≫ (originalLocalCellReplacement S).map (Subdiagram.rightInclusion f t.val) =
                (Subdiagram.inclusion ((originalLocalCellReplacement S).map f) b).right := by
  let R := originalLocalCellReplacement S
  obtain ⟨ν, hν, hLower, hμ, hκ, hUniform⟩ := uniformWeakInterpolation S μ lower
  let : Fact ν.IsRegular := hν
  refine ⟨ν, hν, hLower, hμ, hκ, ?_⟩
  intro X Y f hf s
  have hRf := (originalLocalEquivalence_iff_weak_originalLocalCellReplacement S f).mp hf
  change (data D).model.categoryWithWeakEquivalences.weakEquivalences (R.map f) at hRf
  rw [(data D).weakEquivalences_eq] at hRf
  obtain ⟨⟨hRPL, hRPR, hRRL, hRRR⟩, hFactor⟩ :=
    hUniform (Subdiagram.arrow f s.val) s.property
  obtain ⟨b, p, hB, hBPL, hBPR, hBRL, hBRR, hp⟩ :=
    hFactor (R.map f) hRf (R.mapArrow.map (Subdiagram.inclusion f s.val))
  let B := Subdiagram.arrow (R.map f) b
  let sν : cardinalSubarrowIndex f ν :=
    ⟨s.val, s.property.1.of_le hμ.le, s.property.2.of_le hμ.le⟩
  let : IsCardinalPresentable (R.mapArrow.obj (Subdiagram.arrow f s.val)).left ν := hRRL
  let : IsCardinalPresentable (R.mapArrow.obj (Subdiagram.arrow f s.val)).right ν := hRRR
  let : IsCardinalPresentable B.left ν := hBRL
  let : IsCardinalPresentable B.right ν := hBRR
  obtain ⟨t, hst, q, hpq, hq⟩ :=
    refineUniformTriangle S ν hκ.le f sν B p (Subdiagram.inclusion (R.map f) b) hp
  exact ⟨b, t, hst, p, q, hB, hBPL, hBPR, hBRL, hBRR,
    hRPL, hRPR, hRRL, hRRR, hpq, hp, hq,
    congrArg Arrow.Hom.left hpq, congrArg Arrow.Hom.right hpq,
    congrArg Arrow.Hom.left hp, congrArg Arrow.Hom.right hp,
    congrArg Arrow.Hom.left hq, congrArg Arrow.Hom.right hq⟩

end SimplicialPresheaf.InjectiveKan
