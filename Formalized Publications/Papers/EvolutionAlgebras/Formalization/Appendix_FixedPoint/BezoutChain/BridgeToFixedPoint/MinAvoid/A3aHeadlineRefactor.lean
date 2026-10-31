/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.AvoidanceCoreDimGe3
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.HeightCut.AdditivityClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinSubsetAss
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.A3bMiddleRefactor
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidInstances
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.PrimeSingleClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.RungStepFromUnmixedness
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MkSystemBridge
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungOneClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungRegular
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.MinAtAssCloser
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.TowerReworkFiring
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMQuotientFull
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
/-!
# M-O1b: horth-free A3a headline refactor

Verbatim copy of `minAvoidNonprimeSpec_of_algebraData_of_zNotMem`
(merged here from `Hge2MinAvoidA3aFeed.lean`) minus the `horth` binder.

## Route (load-bearing routing detail)

Do not call the algebra-data wrapper
`minAvoidNonprimeSpec_of_algebraData_of_zClosers` — it demands an
`horth` argument at an explicit position (unprovable without
`horth`). Call `minAvoidNonprimeSpec_of_zClosers` directly: it
takes `(n K c hn hA3a hA3b)` with no algebra data at all
(`AvoidanceCoreDimGe3.lean`); the wrapper's own proof is
just that call (all algebra binders `_`-unused), confirming the
route. The `hA3a` input is discharged by the unconditional add feed
`AdditivityClose.zMemAvoidCloser_unconditional`
(`AdditivityClose.lean`, binders `(K E n hn c V b hexp hN)`,
instance-implicit `htower`/`hcomm` supplied via `have`, matching that lemma's
own `:63-64` pattern). `_hn3` is carried for shape-exactness.

Scope note — headline only: the plug and E10 plug
consume `horth` for real via the R2 `hdiag`/`hsupp` legs
(`AvoidanceCoreDimGe3.lean`). Plug de-horthing is a downstream
wiring step (needs M-O1a's unhorth rung-1 input) — not this leaf.

`[IsAlgClosed K]` is used inside the add feed, via the unconditional
`heightCutAdditivity` (`AdditivityClose.lean` PIT-cut bound,
which requires `[IsAlgClosed K]` per its docstring). Documented here as
`[algClosed]`; no other classical or choice-like axiom is introduced
(see `#print axioms` below).

Status: rung-2 `z ∈ Q` half horth-free; headline conditional-exact on
`[A3b-closer-∀]` given algebra data without `horth`. Note: the
(M-O1b + M-O1c) unconditional reading is prospective — as proved
this leaf still binds `hA3b`; the unconditional headline
materializes only once the downstream A3b feed is supplied (e.g.
`Hge2MinAvoidA3bFinalClose.minAvoidNonprimeSpec_of_algebraData_unconditional`,
which closes A3b via the middle closer but re-adds `horth`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace A3aHeadlineRefactor

open scoped BigOperators

/-- E10 T3 headline with unconditional A3a fed in, without `horth`:
`MinAvoidNonprimeSpec` from consumer algebra data + the A3b closer
alone. The `hA3a` input of
`AvoidanceCoreDimGe3.minAvoidNonprimeSpec_of_zClosers` is discharged by
`AdditivityClose.zMemAvoidCloser_unconditional` (`htower`/`hcomm`
supplied as instances via `have`).

Conditional on exactly `[A3b-closer-∀]` given algebra data,
no `horth`. -/
theorem minAvoidNonprimeSpec_of_algebraData_of_zNotMem_unhorth
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n) (_hn3 : 3 ≤ n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hA3b : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      AvoidanceCoreDimGe3.ZNotMemAvoidCloser n K c hn j) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn := by
  have := htower
  have := hcomm
  exact AvoidanceCoreDimGe3.minAvoidNonprimeSpec_of_zClosers n K c hn
    (AdditivityClose.zMemAvoidCloser_unconditional
      K E n hn c V b hexp hN)
    hA3b

#print axioms minAvoidNonprimeSpec_of_algebraData_of_zNotMem_unhorth

end A3aHeadlineRefactor
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# §§1–5: horth-free `hsucc` at `n = 3` via the master

Full successive regularity of the
bridge system at `n = 3`, ungated (no `horth` anywhere), per-realized-`c`.

## Route (all pins re-read from the proved tree)

* §1 (M-O1d): M-O1c feeds M-O1b `hA3b` (shapes match
  binder-for-binder); `have := htower; have := hcomm` bridges M-O1c's
  instance-implicit tower/comm to M-O1b's explicit binders (M-O1b's own
  `:81-82` pattern). Unconditional given algebra data + `[IsAlgClosed K]`.
* §2: pair-`hsucc` on `prefixPair` at `n = 3` by direct `Fin 2` case
  split (`i.val = 0`: both spans empty, `hreg_rung0`; `i.val = 1`:
  singleton-span congruence with M-O1a at `⟨1, _⟩`).
  unconditional given algebra data + `[IsAlgClosed K]`.
* §3: `HunmixedTwoProp` at J₂ from T3 Target A, transported along the
  proved span bridge `span_prefixPair_rung2` (`extra := {c}`, `hc` by
  `simp`). Conditional-exact on `[FirstReg + C3aGapAll]`.

`C3aGapAll` is closed (`AssociatedPrimes.FiniteDimDischarge`) — `hC3a` binders
below are vestigial; downstream results need only `[FirstReg]`
(see discharge wrappers).
* §4: `AssAvoidRung` at `j = 2` by prime/nonprime split (prime leg is
  the unconditional collapse; nonprime leg is §1 through the
  iff with `Min = Ass` from §3's Prop via the adapter).
  (Verdict note: the per-rung bridge `minEqAssRung_of_hunmixedRung`
  closes `Min ⊆ Ass` internally — no `minSubAss_all` argument.)
* §5: `hsucc` at `n = 3` by direct application of the master —
  `hrung1` is token-identical to M-O1a, T3-B is exactly the
  `hdimEq` binder at `n := 3`, §4 is exactly `hass`. Zero glue.

## Forbidden route (C-O1a)

The plug (`hsucc_of_local_of_supp_of_alloc_of_minAvoidSpec`) is
forbidden and is never referenced here: it takes `HdiagRung1`/`HsuppRung1`
(false at bad-V realized `c`) while M-O1a concludes `IsSMulRegular`
steps — different Props, no transport. This file routes only
(see the route note at §5). MiddleFeed/N3Feed re-pointing is excluded as
moot (M-O1f): nothing on the bypass path imports either feed.

## Status and hygiene

`[IsAlgClosed K]` is used inside the M-O1a/M-O1b/M-O1c feeds (proved
`fewFormsCommonZero` / `heightCutAdditivity`), documented here as
`[algClosed]`; no other classical or choice-like axiom is introduced
(see `#print axioms` below). §§3–5 are `FirstReg`-downstream (T3-A/B take
`[FirstReg + C3aGapAll]` as pass-through Props); this file claims no
unconditional progress and no E4 improvement — E4 is unchanged by L4.
`horth` is never assumed; every statement is per-realized-`c`
(the bare-`∀c` `MinAvoidNonprimeSpec` is false and is never stated).
`repDepth`/`quotExact` occur nowhere here.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace A3aHeadlineRefactor

open scoped BigOperators

universe uK

/-! ## §1. M-O1d: composition → `MinAvoidNonprimeSpec` unconditional -/

/-- M-O1d headline, horth-free: `MinAvoidNonprimeSpec` from consumer
algebra data alone (general `n ≥ 3`). M-O1c's `∀`-closer feeds M-O1b's
`hA3b` directly; the instance/explicit tower-comm mismatch is bridged by
`have`-supplied instances (M-O1b's own `:81-82` pattern).
-/
theorem minAvoidNonprimeSpec_unhorth_of_algebraData
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n) (hn3 : 3 ≤ n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn := by
  have := htower
  have := hcomm
  exact A3aHeadlineRefactor.minAvoidNonprimeSpec_of_algebraData_of_zNotMem_unhorth
    K E n hn hn3 c V b hexp hN htower hcomm
    (A3bMiddleRefactor.zNotMemAvoidCloser_unhorth_forall
      K E n hn c V b hexp hN)

#print axioms minAvoidNonprimeSpec_unhorth_of_algebraData

/-! ## §2. Pair-`hsucc` on `prefixPair` at `n = 3` -/

/-- Pair-`hsucc` at `n = 3`, horth-free: successive regularity of
`prefixPair` from algebra data. Direct `Fin 2` case split: at `i.val = 0`
both prefix spans are empty (`hreg_rung0`); at `i.val = 1` both sides are
singletons of the rung-0 equation (M-O1a at `⟨1, _⟩`), closed by
set-equality → span-congruence → element rewrite.
-/
theorem hsucc_prefixPair_n3_unhorth
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (hn : 0 < 3) (hn2 : 2 ≤ 3)
    (c : Fin 3 → Fin 3 → Fin 3 → K)
    (V : Submodule K E) (b : Module.Basis (Fin 3) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    RegularityBridge.SuccessiveSMulRegular
      (RungStepFromUnmixedness.prefixPair 3 K c hn hn2) := by
  have hs3 : statementIndex 3 + 1 = 3 := shift_add_one 3 hn
  let k0 : Fin (statementIndex 3 + 1) := ⟨0, by omega⟩
  let k1 : Fin (statementIndex 3 + 1) := ⟨1, by omega⟩
  have hk0v : k0.val = 0 := rfl
  have hk1v : k1.val = 1 := rfl
  have hrung1 := RungOneClose.rung1step_unhorth_of_algebraData
    K E V 3 hn c b hexp hN htower hcomm
  have hpair0 : (RungStepFromUnmixedness.prefixPair 3 K c hn hn2)
      (⟨0, by decide⟩ : Fin 2) = (bridgeSystem 3 K c hn) k0 :=
    congrArg (bridgeSystem 3 K c hn) (Fin.ext hk0v.symm)
  intro i
  have hlt := i.isLt
  by_cases h0 : i.val = 0
  · -- Rung 0: both prefix spans are empty.
    have hset : Set.image (RungStepFromUnmixedness.prefixPair 3 K c hn hn2)
        {j : Fin 2 | j.val < i.val} = ∅ := by
      rw [h0]
      have hempty : ({j : Fin 2 | j.val < 0} : Set (Fin 2)) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro j hj
        simp only [Set.mem_ofPred_eq] at hj
        omega
      rw [hempty]
      simp
    have hspan0 : Ideal.span (Set.image
        (RungStepFromUnmixedness.prefixPair 3 K c hn hn2)
        {j : Fin 2 | j.val < i.val}) = ⊥ := by
      rw [hset, Ideal.span_empty]
    have hreg0 := RungRegular.hreg_rung0 K 3 hn c k0 hk0v
    rw [hk0v, List.take_zero, Ideal.ofList_nil] at hreg0
    have ei0 : i = (⟨0, by decide⟩ : Fin 2) := Fin.ext h0
    have helem : (RungStepFromUnmixedness.prefixPair 3 K c hn hn2) i =
        (bridgeSystem 3 K c hn) k0 := by
      rw [ei0]
      exact hpair0
    rw [hspan0, helem]
    exact hreg0
  · -- Rung 1: singleton-span congruence with M-O1a.
    have h1 : i.val = 1 := by omega
    have hspan1 : Ideal.span (Set.image
        (RungStepFromUnmixedness.prefixPair 3 K c hn hn2)
        {j : Fin 2 | j.val < i.val}) =
        Ideal.span (Set.image (bridgeSystem 3 K c hn)
          {k' : Fin (statementIndex 3 + 1) | k'.val < k1.val}) := by
      rw [h1, hk1v]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨j, hj, rfl⟩
        have hj0 : j.val = 0 := by omega
        have ej : j = (⟨0, by decide⟩ : Fin 2) := Fin.ext hj0
        refine ⟨k0, by omega, ?_⟩
        rw [ej]
        exact hpair0.symm
      · rintro ⟨k', hk', rfl⟩
        have hk'0 : k'.val = 0 := by omega
        have ek' : k' = k0 := Fin.ext (by omega)
        refine ⟨⟨0, by decide⟩, by decide, ?_⟩
        rw [ek']
        exact hpair0
    have ei1 : i = (⟨1, by decide⟩ : Fin 2) := Fin.ext h1
    have helem : (RungStepFromUnmixedness.prefixPair 3 K c hn hn2) i =
        (bridgeSystem 3 K c hn) k1 := by
      rw [ei1]
      exact congrArg (bridgeSystem 3 K c hn) (Fin.ext hk1v.symm)
    rw [hspan1, helem]
    exact hrung1 k1 hk1v

#print axioms hsucc_prefixPair_n3_unhorth

/-! ## §3. `HunmixedTwoProp` at J₂ -/

/-- `HunmixedTwoProp` at J₂, horth-free: unmixedness of the rung-2 pair
span from T3 Target A (`extra := {c}`), transported along the proved
span bridge `span_prefixPair_rung2`. No custom span arithmetic.

Conditional on exactly `[hsucc₂, FirstReg + C3aGapAll]` given
`[IsAlgClosed K]`. -/
theorem hunmixedTwoProp_j2_n3_of_cm (K : Type uK) [Field K] [IsAlgClosed K]
    (hn : 0 < 3) (hn2 : 2 ≤ 3)
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hC3a : CMQuotientFull.C3aGapAll.{uK})
    (c : Fin 3 → Fin 3 → Fin 3 → K)
    (hsucc₂ : RegularityBridge.SuccessiveSMulRegular
      (RungStepFromUnmixedness.prefixPair 3 K c hn hn2)) :
    UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 3 + 2) K
      (RungStepFromUnmixedness.prefixPair 3 K c hn hn2) hsucc₂ _ rfl := by
  have hc : c ∈ MinAtAssCloser.RB4Cset K {c} := by
    unfold MinAtAssCloser.RB4Cset
    simp
  have hdimEq := TowerReworkFiring.hdimEqMinAtAss_j2_of_cm
    K hn {c} hFR hC3a c hc
  have hspan := RungStepFromUnmixedness.span_prefixPair_rung2 K 3 hn hn2 c
    (MinAvoidInstances.gapRung2 hn) rfl
  have hdimEq' : UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex 3 + 2) K
      (Ideal.span (Set.range
        (RungStepFromUnmixedness.prefixPair 3 K c hn hn2))) := by
    rw [hspan]
    exact hdimEq
  exact UnmixednessAtLengthTwo.hunmixed_two_forall_of_hdimEqMin (statementIndex 3 + 2) K
    _ hsucc₂ _ rfl hdimEq'

#print axioms hunmixedTwoProp_j2_n3_of_cm

/-! ## §4. hass-n3: `AssAvoidRung` at `j = 2` -/

/-- hass at `n = 3`, horth-free: `AssAvoidRung` at every rung `≥ 2`
(the single rung `j = 2`) from algebra data + §3's Prop + §1 at `n := 3`.
Prime stages collapse unconditionally; nonprime stages go
through the iff with `Min = Ass` from §3's Prop via the
adapter, transported along `hj2` + §3's span bridge.

Conditional on exactly `[hsucc₂, hU, FirstReg + C3aGapAll]`
given algebra data + `[IsAlgClosed K]`. -/
theorem assAvoid_n3_unhorth (K : Type uK) [Field K] [IsAlgClosed K]
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (hn : 0 < 3) (hn2 : 2 ≤ 3)
    (c : Fin 3 → Fin 3 → Fin 3 → K)
    (V : Submodule K E) (b : Module.Basis (Fin 3) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hsucc₂ : RegularityBridge.SuccessiveSMulRegular
      (RungStepFromUnmixedness.prefixPair 3 K c hn hn2))
    (hU : UnmixednessAtLengthTwo.HunmixedTwoProp (statementIndex 3 + 2) K
      (RungStepFromUnmixedness.prefixPair 3 K c hn hn2) hsucc₂ _ rfl) :
    ∀ j : Fin (statementIndex 3 + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung 3 K c hn j := by
  have hspec := minAvoidNonprimeSpec_unhorth_of_algebraData K E 3 hn
    (le_refl 3) c V b hexp hN htower hcomm
  intro j hj
  have h3 : statementIndex 3 + 1 = 3 := shift_add_one 3 hn
  have hj2 : j.val = 2 := by
    have hlt : j.val < statementIndex 3 + 1 := j.isLt
    omega
  by_cases hP : (MinAvoidRungs.stageIdeal 3 K c hn j).IsPrime
  · have := hP
    exact PrimeSingleClose.assAvoidRung_of_prime_unconditional
      3 K c hn j
  · have hmin := hspec j hj hP
    have hU' := RungStepFromUnmixedness.hunmixed_forall_of_hunmixedTwoProp
      (statementIndex 3 + 2) K
      (RungStepFromUnmixedness.prefixPair 3 K c hn hn2) hsucc₂ _ rfl hU
    have hspan := RungStepFromUnmixedness.span_prefixPair_rung2 K 3 hn hn2 c j hj2
    rw [hspan] at hU'
    have heq := MinSubsetAss.minEqAssRung_of_hunmixedRung 3 K c hn j hU'
    exact (MinAvoidRungs.minAvoidRung_iff_assAvoidRung_of_minEqAss
      3 K c hn j heq).mp hmin

#print axioms assAvoid_n3_unhorth

/-! ## §5. hsucc-n3 -/

/-- Full `hsucc` at `n = 3`, horth-free: successive regularity of the
bridge triple from algebra data. Direct application of the
master — `hrung1` is token-identical to M-O1a, T3-B is exactly the
`hdimEq` binder at `n := 3`, §4 is exactly `hass`. Zero glue.

route note (C-O1a): this section routes only. The
plug is forbidden (type mismatch + false target — see the module
docstring) and the wrapper is skipped (same master with rung 1
via `hdich`; L4 feeds directly).

Conditional on exactly `[FirstReg + C3aGapAll]` given algebra
data + `[IsAlgClosed K]`. -/
theorem hsucc_bridgeSystem_n3_unhorth (K : Type uK) [Field K] [IsAlgClosed K]
    (E : Type*) [NonUnitalNonAssocSemiring E] [Module K E]
    (hn : 0 < 3)
    (c : Fin 3 → Fin 3 → Fin 3 → K)
    (V : Submodule K E) (b : Module.Basis (Fin 3) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hFR : CMQuotientFull.FirstReg.{uK, uK})
    (hC3a : CMQuotientFull.C3aGapAll.{uK}) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem 3 K c hn) := by
  have hn2 : 2 ≤ 3 := by decide
  have hrung1 := RungOneClose.rung1step_unhorth_of_algebraData
    K E V 3 hn c b hexp hN htower hcomm
  have hc : c ∈ MinAtAssCloser.RB4Cset K {c} := by
    unfold MinAtAssCloser.RB4Cset
    simp
  have hdimEq := TowerReworkFiring.hdimEq_rung2_binder_j2_of_cm
    K hn {c} hFR hC3a c hc
  have hsucc₂ := hsucc_prefixPair_n3_unhorth K E hn hn2 c V b hexp hN
    htower hcomm
  have hU := hunmixedTwoProp_j2_n3_of_cm K hn hn2 hFR hC3a c hsucc₂
  have hass := assAvoid_n3_unhorth K E hn hn2 c V b hexp hN htower hcomm
    hsucc₂ hU
  exact MinSubsetAss.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_assAvoid
    K 3 hn c hrung1 hdimEq hass

#print axioms hsucc_bridgeSystem_n3_unhorth

end A3aHeadlineRefactor
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
