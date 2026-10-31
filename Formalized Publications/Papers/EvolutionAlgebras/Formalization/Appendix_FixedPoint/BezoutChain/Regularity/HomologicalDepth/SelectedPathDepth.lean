/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMQuotientFull
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMQuotientGreedyTower
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.QuotientByRegularIsCM
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMPositiveDimHasDepth
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMDepthSubstitution
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
/-!
# Per-`Q` selected path depth from CM (E5 assembly)

`C3aGapAll` is closed (`AssociatedPrimes.FiniteDimDischarge`) — `hC3a` binders
below are vestigial; downstream results need only `[FirstReg]`
(see discharge wrappers).

Proves `supPathDepthSel_bot_of_cm`: over `R_Q = Localization.AtPrime Q`,
selected path depth at `⊥` holds conditional only on the pass-through
residuals `[FirstReg + C3aGapAll]` (no dimension hypothesis; the CM leg
covers every `Q`, closing the dim-≥-2 slice of O2 since dim-≤-1 is closed
unconditionally elsewhere).

Route:
* Lemma A (`supTowerReachSel_le_maximal`): Sel-reachable ideals lie in `𝔪`
  (reachability induction; `SupSelectData.1` is `y ∈ 𝔪`).
* Scalar bridge (`isSMulRegular_quotient_mk_of_isSMulRegular`): R-scalar
  `y`-regularity on `R ⧸ J'` gives self-scalar `mk y`-regularity
  (quotient-smul agreement on `mk`-surjective generators).
* Lemma B (internal `hCM`): Sel-reachable quotients are CM (C2 copy) —
  base from `isCM_atPrime_of_residuals` + `greedy_of_residuals` across
  `quotientBot` (C3 `:806–:819` pattern); step via the C2 main theorem +
  double-quotient re-presentation across three ring equivs.
* Main: SUBST close
  (`maximalIdeal_notMem_associatedPrimes_of_cm_quotient_subst`).

Residuals: pass-through `[FirstReg + C3aGapAll]` only (binders); `hQ` is
kept unused for the E4 call-site shape. Cycle hygiene: consumes
CM-ness, never proves it from depth.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SelectedPathDepth

universe uK

/-! ## Lemma A: Sel-reachable ideals lie in `𝔪` -/

/-- Sel-reachable ideals from `⊥` lie in the maximal ideal: base `⊥ ≤ 𝔪`
is `bot_le`; the step uses `SupSelectData.1` (`y ∈ 𝔪`).
-/
theorem supTowerReachSel_le_maximal {R : Type*} [CommRing R] [IsLocalRing R]
    (J' : Ideal R)
    (h : ColonTransfer.SupTowerReachSel (R := R) ⊥ J') :
    J' ≤ IsLocalRing.maximalIdeal R := by
  induction h with
  | base => exact bot_le
  | step _ hstep ih =>
      obtain ⟨y, heq, hsel, _⟩ := hstep
      rw [heq]
      exact sup_le ih ((Ideal.span_singleton_le_iff_mem _).mpr hsel.1)

#print axioms supTowerReachSel_le_maximal

/-! ## Scalar bridge: R-scalar regularity to self-scalar regularity -/

/-- The single-element scalar bridge (C3 note, finding F5):
R-scalar `y`-regularity on `R ⧸ J'` (`SupT1Data.1` form) gives
self-scalar `mk y`-regularity (C2-step form), by smul-agreement on
`mk`-surjective generators via quotient-smul simp lemmas.
-/
theorem isSMulRegular_quotient_mk_of_isSMulRegular {R : Type*} [CommRing R]
    (J' : Ideal R) (y : R)
    (hreg : IsSMulRegular (R ⧸ J') y) :
    IsSMulRegular (R ⧸ J') (Ideal.Quotient.mk J' y) := by
  have hagree : ∀ x : R ⧸ J',
      y • x = (Ideal.Quotient.mk J' y) • x := by
    intro x
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [smul_eq_mul, ← map_mul, ← Ideal.Quotient.mk_eq_mk,
      ← Submodule.Quotient.mk_smul, smul_eq_mul]
    exact Ideal.Quotient.mk_eq_mk _
  intro a b hab
  apply hreg
  change y • a = y • b
  rw [hagree, hagree]
  exact hab

#print axioms isSMulRegular_quotient_mk_of_isSMulRegular

/-! ## Main: `supPathDepthSel_bot_of_cm` -/

/-- E5 assembly: per-`Q` selected path depth at `⊥`, conditional only on
the pass-through `[FirstReg + C3aGapAll]`. Stated on the C1FullTower
universe diagonal: the C4→C1-base handoff forces the full `uK` diagonal
(finding F2), so the binders are `FirstReg.{uK,uK}` / `C3aGapAll.{uK}`.
`hQ` is unused in the body (kept for the E4 call-site shape).

Conditional on exactly `[FirstReg + C3aGapAll]`. -/
theorem supPathDepthSel_bot_of_cm (m : ℕ) (K : Type uK) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hC3a : CMQuotientFull.C3aGapAll.{uK}) :
    ColonTransfer.SupPathDepthSel
      (R := Localization.AtPrime Q) ⊥ := by
  have _hQuse := hQ
  -- The C2-input gap hypothesis, rewrapped from `hC3a` (finding F1 fix).
  have hgap : ∀ (T : Type uK) [CommRing T] [IsLocalRing T]
      [IsNoetherianRing T] (q : Ideal T) [q.IsPrime],
      ringKrullDim T < ⊤ →
      QuotientByRegularIsCM.IsCM T → CMPositiveDimHasDepth.C3aGap T q :=
    fun (T : Type uK) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
      (q : Ideal T) [q.IsPrime] (hfin : ringKrullDim T < ⊤)
      (hCM : QuotientByRegularIsCM.IsCM T) =>
      hC3a T q hfin (CMDepthSubstitution.isCM_c3_of_c2 hCM)
  -- C1 base at `R_Q`, via C4 at `n := spanFinrank 𝔪_Q`.
  have hSK : CMQuotientFull.GreedyOfResiduals.{uK, uK, uK, uK, uK}
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank :=
    CMQuotientGreedyTower.greedy_of_residuals _
  have hC1base :=
    CMQuotientFull.isCM_atPrime_of_residuals m K Q hFR hC3a hSK
  have hC3base : CMPositiveDimHasDepth.IsCM (Localization.AtPrime Q) :=
    (CMQuotientFull.isCM_c1_iff_c3 _).mp hC1base
  -- Lemma B: Sel-reachable quotients are CM (C2 copy). The local-ring
  -- instance rides as a `∀`-binder (C3 precedent); each case
  -- supplies it from Lemma A via the C2 companion.
  have hCM : ∀ (J' : Ideal (Localization.AtPrime Q))
      (hreach : ColonTransfer.SupTowerReachSel
        (R := Localization.AtPrime Q) ⊥ J')
      [IsLocalRing ((Localization.AtPrime Q) ⧸ J')],
      QuotientByRegularIsCM.IsCM ((Localization.AtPrime Q) ⧸ J') := by
    intro J' hreach
    induction hreach with
    | base =>
        have hlocBot : IsLocalRing ((Localization.AtPrime Q) ⧸
            (⊥ : Ideal (Localization.AtPrime Q))) :=
          QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal ⊥ bot_le
        -- Base `hmap`: copy-adapt of C3 `:806–:819`.
        have hmapQ : Ideal.map
            (RingEquiv.quotientBot (Localization.AtPrime Q)).symm.toRingHom
            (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
            = IsLocalRing.maximalIdeal ((Localization.AtPrime Q) ⧸
              (⊥ : Ideal (Localization.AtPrime Q))) := by
          rw [CMDepthSubstitution.hC2comp_discharged _ bot_le]
          have hFG : (RingEquiv.quotientBot
              (Localization.AtPrime Q)).symm.toRingHom
              = Ideal.Quotient.mk ⊥ := by
            ext x
            change (RingEquiv.quotientBot
              (Localization.AtPrime Q)).symm x
              = Ideal.Quotient.mk ⊥ x
            apply (RingEquiv.quotientBot
              (Localization.AtPrime Q)).injective
            rw [(RingEquiv.quotientBot
              (Localization.AtPrime Q)).apply_symm_apply,
              RingEquiv.quotientBot_mk]
          rw [hFG]
        have hCMbotC3 : CMPositiveDimHasDepth.IsCM ((Localization.AtPrime Q) ⧸
            (⊥ : Ideal (Localization.AtPrime Q))) :=
          CMPositiveDimHasDepth.isCM_ringEquiv_congr
            (RingEquiv.quotientBot (Localization.AtPrime Q)).symm
            hmapQ hC3base
        have hCMbot : QuotientByRegularIsCM.IsCM ((Localization.AtPrime Q) ⧸
            (⊥ : Ideal (Localization.AtPrime Q))) :=
          CMDepthSubstitution.isCM_c2_of_c3 hCMbotC3
        intro _
        exact hCMbot
    | step hreach hstep ih =>
        clear J'
        rename_i J' J''
        obtain ⟨y, heq, hsel, ht1⟩ := hstep
        have hym : y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
          hsel.1
        have hregR : IsSMulRegular ((Localization.AtPrime Q) ⧸ J') y :=
          ht1.1
        have hleJ' : J' ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
          supTowerReachSel_le_maximal J' hreach
        have hlocJ' : IsLocalRing ((Localization.AtPrime Q) ⧸ J') :=
          QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal J' hleJ'
        have ihCM : QuotientByRegularIsCM.IsCM ((Localization.AtPrime Q) ⧸ J') :=
          ih
        have hmem : Ideal.Quotient.mk J' y ∈ IsLocalRing.maximalIdeal
            ((Localization.AtPrime Q) ⧸ J') := by
          rw [QuotientByRegularIsCM.maximalIdeal_quotient_eq_map J' hleJ']
          exact Ideal.mem_map_of_mem _ hym
        have hregMk : IsSMulRegular ((Localization.AtPrime Q) ⧸ J')
            (Ideal.Quotient.mk J' y) :=
          isSMulRegular_quotient_mk_of_isSMulRegular J' y hregR
        have hspanMk_le : Ideal.span {Ideal.Quotient.mk J' y}
            ≤ IsLocalRing.maximalIdeal ((Localization.AtPrime Q) ⧸ J') :=
          (Ideal.span_singleton_le_iff_mem _).mpr hmem
        have hlocSpan : IsLocalRing (((Localization.AtPrime Q) ⧸ J')
            ⧸ Ideal.span {Ideal.Quotient.mk J' y}) :=
          QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hspanMk_le
        have hCM1 : QuotientByRegularIsCM.IsCM (((Localization.AtPrime Q) ⧸ J')
            ⧸ Ideal.span {Ideal.Quotient.mk J' y}) :=
          QuotientByRegularIsCM.isCM_quotient_of_isSMulRegular ihCM hmem hregMk
        have hspan_le : Ideal.span {y}
            ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
          (Ideal.span_singleton_le_iff_mem _).mpr hym
        have hleSup : J' ⊔ Ideal.span {y}
            ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
          sup_le hleJ' hspan_le
        have hJle : Ideal.map (Ideal.Quotient.mk J') (Ideal.span {y})
            ≤ IsLocalRing.maximalIdeal ((Localization.AtPrime Q) ⧸ J') := by
          rw [QuotientByRegularIsCM.maximalIdeal_quotient_eq_map J' hleJ']
          exact Ideal.map_mono hspan_le
        have hmap_span : Ideal.map (Ideal.Quotient.mk J') (Ideal.span {y})
            = Ideal.span {Ideal.Quotient.mk J' y} := by
          rw [Ideal.map_span, Set.image_singleton]
        have hlocMap : IsLocalRing (((Localization.AtPrime Q) ⧸ J')
            ⧸ Ideal.map (Ideal.Quotient.mk J') (Ideal.span {y})) :=
          QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hJle
        have hleJ'' : J'' ≤ IsLocalRing.maximalIdeal
            (Localization.AtPrime Q) := by
          rw [heq]
          exact hleSup
        have hlocSup : IsLocalRing ((Localization.AtPrime Q)
            ⧸ (J' ⊔ Ideal.span {y})) :=
          QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hleSup
        have hlocJ'' : IsLocalRing ((Localization.AtPrime Q) ⧸ J'') :=
          QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hleJ''
        have hmap1 : Ideal.map (Ideal.quotEquivOfEq hmap_span).symm.toRingHom
            (IsLocalRing.maximalIdeal (((Localization.AtPrime Q) ⧸ J')
              ⧸ Ideal.span {Ideal.Quotient.mk J' y}))
            = IsLocalRing.maximalIdeal (((Localization.AtPrime Q) ⧸ J')
              ⧸ Ideal.map (Ideal.Quotient.mk J') (Ideal.span {y})) :=
          CMPositiveDimHasDepth.map_quotEquivOfEq_symm_maximal _ _
            hmap_span CMDepthSubstitution.hC2comp_discharged
            hJle hspanMk_le
        have hmap2 : Ideal.map (DoubleQuot.quotQuotEquivQuotSup J'
              (Ideal.span {y})).toRingHom
            (IsLocalRing.maximalIdeal (((Localization.AtPrime Q) ⧸ J')
              ⧸ Ideal.map (Ideal.Quotient.mk J') (Ideal.span {y})))
            = IsLocalRing.maximalIdeal ((Localization.AtPrime Q)
              ⧸ (J' ⊔ Ideal.span {y})) :=
          CMPositiveDimHasDepth.map_quotQuotEquiv_maximal _ _
            CMDepthSubstitution.hC2comp_discharged hleJ' hJle hleSup
        have hmap3 : Ideal.map (Ideal.quotEquivOfEq heq).symm.toRingHom
            (IsLocalRing.maximalIdeal ((Localization.AtPrime Q)
              ⧸ (J' ⊔ Ideal.span {y})))
            = IsLocalRing.maximalIdeal ((Localization.AtPrime Q) ⧸ J'') :=
          CMPositiveDimHasDepth.map_quotEquivOfEq_symm_maximal _ _
            heq CMDepthSubstitution.hC2comp_discharged hleJ'' hleSup
        have hCM1c3 : CMPositiveDimHasDepth.IsCM (((Localization.AtPrime Q) ⧸ J')
            ⧸ Ideal.span {Ideal.Quotient.mk J' y}) :=
          CMDepthSubstitution.isCM_c3_of_c2 hCM1
        have hCMmap : CMPositiveDimHasDepth.IsCM (((Localization.AtPrime Q) ⧸ J')
            ⧸ Ideal.map (Ideal.Quotient.mk J') (Ideal.span {y})) :=
          CMPositiveDimHasDepth.isCM_ringEquiv_congr
            (Ideal.quotEquivOfEq hmap_span).symm hmap1 hCM1c3
        have hCMsup : CMPositiveDimHasDepth.IsCM ((Localization.AtPrime Q)
            ⧸ (J' ⊔ Ideal.span {y})) :=
          CMPositiveDimHasDepth.isCM_ringEquiv_congr
            (DoubleQuot.quotQuotEquivQuotSup J' (Ideal.span {y}))
            hmap2 hCMmap
        have hCMstep : QuotientByRegularIsCM.IsCM
            ((Localization.AtPrime Q) ⧸ J'') :=
          CMDepthSubstitution.isCM_c2_of_c3
            (CMPositiveDimHasDepth.isCM_ringEquiv_congr
              (Ideal.quotEquivOfEq heq).symm hmap3 hCMsup)
        intro _
        exact hCMstep
  -- Main close: SUBST on the Lemma-B CM fact; `hpos` passes through.
  intro J' hreach hpos
  have hleJ' : J' ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    supTowerReachSel_le_maximal J' hreach
  have hlocJ' : IsLocalRing ((Localization.AtPrime Q) ⧸ J') :=
    QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal J' hleJ'
  have hCMJ' : QuotientByRegularIsCM.IsCM ((Localization.AtPrime Q) ⧸ J') :=
    hCM J' hreach
  have hfinRQ : ringKrullDim (Localization.AtPrime Q) < ⊤ :=
    lt_of_le_of_lt
      (CMQuotientFull.dim_atPrime_le_spanFinrank m K Q)
      (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))
  exact CMDepthSubstitution.maximalIdeal_notMem_associatedPrimes_of_cm_quotient_subst
    J' hCMJ' hpos hgap hfinRQ

#print axioms supPathDepthSel_bot_of_cm

end SelectedPathDepth
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# `hdepth_stage` / `hdepth_full` from the CM residuals

Proves the two assembly theorems closing the R4c
open hypotheses `hdepth_stage` / `hdepth_full`
(`UngatedHres2Assembly.lean`, repeated in the E3 plug at
`Hres2PlugCorollary.lean`) by instantiating the proved E5 engine
`SelectedPathDepth.supPathDepthSel_bot_of_cm`
(`SelectedPathDepth.lean`) at `m := statementIndex n + 2`, with `J`
the stage ideal (stage) or the full-span ideal (full) and `Q`, `[Q.IsPrime]`,
`hQ`, `hFR`, `hC3a` passed through verbatim.

Universe diagonal: E5 is `uK`-monomorphic (`FirstReg.{uK,uK}` /
`C3aGapAll.{uK}`), so this leaf is stated at `universe uK` with
`K : Type uK`; feeding the conclusions into R4c's `∀ K : Type*` master
instantiates R4c's `K` at `uK` (legal; the gated conclusion is then
`uK`-monomorphic).

`C3aGapAll` is closed (`AssociatedPrimes.FiniteDimDischarge`) — `hC3a` binders
below are vestigial; downstream results need only `[FirstReg]`
(see discharge wrappers).

Conditional on exactly `[FirstReg + C3aGapAll]`. Nothing new assumed
(`hQ` is a per-`(n, c, j, Q)` conclusion binder, not an assumption). Fresh
leaf: existing files untouched, acyclic by construction (nothing imports this
leaf).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KoszulSupHdepthAssemble

universe uK

/-- R4c `hdepth_stage` from the CM residuals: `SupPathDepthSel ⊥` at every
stage ideal, via `supPathDepthSel_bot_of_cm` at `m := statementIndex n + 2`
with `J := MinAvoidRungs.stageIdeal n K c hn j`.

Conditional on exactly `[FirstReg + C3aGapAll]`. -/
theorem hdepth_stage_of_cm_residuals
    (K : Type uK) [Field K]
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hC3a : CMQuotientFull.C3aGapAll.{uK}) :
    ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)),
      ∀ (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ MinAvoidRungs.stageIdeal n K c hn j) →
      ColonTransfer.SupPathDepthSel
        (R := Localization.AtPrime Q) ⊥ := by
  intro n hn c j Q _ hQ
  exact SelectedPathDepth.supPathDepthSel_bot_of_cm (statementIndex n + 2) K
    (MinAvoidRungs.stageIdeal n K c hn j) Q hQ hFR hC3a

#print axioms hdepth_stage_of_cm_residuals

/-- R4c `hdepth_full` from the CM residuals: `SupPathDepthSel ⊥` at every
full-span ideal, via `supPathDepthSel_bot_of_cm` at
`m := statementIndex n + 2` with
`J := Ideal.span (Set.range (bridgeSystem n K c hn))`.

Conditional on exactly `[FirstReg + C3aGapAll]`. -/
theorem hdepth_full_of_cm_residuals
    (K : Type uK) [Field K]
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hC3a : CMQuotientFull.C3aGapAll.{uK}) :
    ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ Ideal.span (Set.range (bridgeSystem n K c hn))) →
      ColonTransfer.SupPathDepthSel
        (R := Localization.AtPrime Q) ⊥ := by
  intro n hn c Q _ hQ
  exact SelectedPathDepth.supPathDepthSel_bot_of_cm (statementIndex n + 2) K
    (Ideal.span (Set.range (bridgeSystem n K c hn))) Q hQ hFR hC3a

#print axioms hdepth_full_of_cm_residuals

end KoszulSupHdepthAssemble
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
