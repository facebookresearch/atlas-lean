/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Monadic
public import Mathlib.Tactic.NormNum

/-!
# Tests for monadic adversaries

Toy computations exercising the public behavior of `CSLibExt.Crypto.Framework.Monadic`. Each
computed value would change under a different semantics.

* **Transcripts.** `sampleQuery` samples a uniform bit `b`, queries the oracle at `b` and
  outputs the answer. Against the oracle `x ↦ !x`, its `mEvalLog` transcript is exactly
  `[(b, !b)]`: the query is recorded and the sampling step is not
  (`mEvalLog_sampleQuery`, `mEvalLog_sampleQuery_length`).
* **Cost classes.** `sampleQuery` makes one oracle query and one sampling step: it is
  `OracleBounded 1` and `SampleBounded 1`, but neither `OracleBounded 0` nor `SampleBounded 0`.
* **Simulation.** `bitSub` answers every query with a fresh uniform bit and makes no query.
  Simulating the uniform oracle by `bitSub` keeps the output of `sampleQuery` uniform
  (`evalPMF_simulate`), leaves no oracle query (`oracleBounded_simulate`: `1 * 0`), and costs
  two sampling steps (`sampleBounded_simulate`: `1 + 1 * 1`), both of which occur on every path,
  so the simulation is not `SampleBounded 1`.
* **`ofCoins`, MAC.** Against the toy MAC `tag k m = k + m` on `ZMod 2`, the coin forger
  `macForger` (query `0`, then forge `(1, t + 1)`) wins with probability `1` in the coin game, and
  so, by `mMacGame_ofCoins`, in the monadic game of `MMACForger.ofCoins macForger`, which makes
  one query and one sampling step. The monadic forger `guessForger` samples its tag offset after
  its query and wins with probability `1/2`.
* **`ofCoins`, CPA.** Against the deterministic pad `Enc_k(m) = k + m` on `ZMod 2`, the coin
  adversary `padAdv` (query `Enc_k(0) = k`, then unmask the challenge) outputs the challenge bit
  in the monadic experiment of `MCPAAdversary.ofCoins padAdv`, so its monadic CPA advantage is
  `1/2`, the largest possible.
-/

@[expose] public section

namespace Cslib.Crypto.FrameworkTests.Monadic

open Cslib.Crypto.Framework FreeM OracleComp

/-! ### A computation that samples, then queries -/

/-- The sampling family drawing a uniform bit. -/
noncomputable abbrev Bits : SampleFam.{0} := coinFam fairCoin

/-- Sample a uniform bit `b`, query the oracle at `b`, and output the answer. -/
noncomputable def sampleQuery : (WithSample Bits (OracleSig Bool Bool)).FreeM Bool :=
  sampleThen PUnit.unit fun b => queryThen b fun y => pure y

/-- The deterministic oracle answering the query `x` with `!x`. -/
noncomputable def negOracle : Bool → PMF Bool := fun x => PMF.pure (!x)

/-! ### Transcripts -/

/-- The transcript of `sampleQuery` is the query `(b, !b)` alone: the sampled bit `b` appears
only as the query, never as an entry of its own. -/
theorem mEvalLog_sampleQuery :
    mEvalLog Bits negOracle sampleQuery = fairCoin.bind fun b => PMF.pure (!b, [(b, !b)]) := by
  simp [sampleQuery, negOracle, PMF.pure_map]

/-- Every transcript of `sampleQuery` has exactly one entry; recording the sampling step would
give two. -/
theorem mEvalLog_sampleQuery_length :
    (mEvalLog Bits negOracle sampleQuery).map (fun p => p.2.length) = PMF.pure 1 := by
  rw [mEvalLog_sampleQuery, PMF.map_bind]
  simp [PMF.pure_map]

/-! ### Cost classes -/

/-- `sampleQuery` makes at most one oracle query along every path. -/
theorem sampleQuery_oracleBounded : OracleBounded 1 sampleQuery :=
  oracleBoundedWith_sampleThen fun _ =>
    (FreeM.costBoundedWith_liftBind_of_costly rfl 0).mpr fun _ => trivial

/-- The query is counted: `sampleQuery` is not `OracleBounded 0`. -/
theorem not_sampleQuery_oracleBounded_zero : ¬ OracleBounded 0 sampleQuery := fun h =>
  FreeM.not_costBoundedWith_zero_of_costly rfl
    ((FreeM.costBoundedWith_liftBind_of_free rfl 0).mp h true)

/-- `sampleQuery` makes at most one sampling step along every path. -/
theorem sampleQuery_sampleBounded : SampleBounded 1 sampleQuery :=
  sampleBoundedWith_sampleThen fun _ =>
    (FreeM.costBoundedWith_liftBind_of_free rfl 0).mpr fun _ => trivial

/-- The sampling step is counted: `sampleQuery` is not `SampleBounded 0`. -/
theorem not_sampleQuery_sampleBounded_zero : ¬ SampleBounded 0 sampleQuery :=
  FreeM.not_costBoundedWith_zero_of_costly rfl

/-! ### Simulation -/

/-- The subroutine answering every query with a fresh uniform bit, without querying. -/
noncomputable def bitSub : Bool → (WithSample Bits (OracleSig Bool Bool)).FreeM Bool :=
  fun _ => sampleThen PUnit.unit fun b => pure b

/-- `bitSub` has the distribution of the uniform oracle, whatever oracle it runs against. -/
theorem evalPMF_bitSub (O' : Bool → PMF Bool) (a : Bool) :
    evalPMF (withSampleOracle Bits O') (bitSub a) = fairCoin := by
  simp [bitSub]

/-- **Simulation preserves the output distribution**: simulating the uniform oracle by `bitSub`
keeps the output of `sampleQuery` uniform, whatever oracle the simulation runs against. -/
theorem evalPMF_simulate_sampleQuery (O' : Bool → PMF Bool) :
    evalPMF (withSampleOracle Bits O') (simulate bitSub sampleQuery) = fairCoin := by
  rw [evalPMF_simulate (O := fun _ => fairCoin) (evalPMF_bitSub O')]
  simp [sampleQuery]

/-- The simulation makes no oracle query: `1 * 0` by `oracleBounded_simulate`. -/
theorem simulate_sampleQuery_oracleBounded : OracleBounded 0 (simulate bitSub sampleQuery) :=
  oracleBounded_simulate (q' := 0)
    (fun _ => oracleBoundedWith_sampleThen fun _ => (FreeM.costBoundedWith_pure _ _).mpr trivial)
    sampleQuery_oracleBounded

/-- The simulation makes at most two sampling steps: `1 + 1 * 1` by `sampleBounded_simulate`. -/
theorem simulate_sampleQuery_sampleBounded : SampleBounded 2 (simulate bitSub sampleQuery) :=
  sampleBounded_simulate (s' := 1)
    (fun _ => sampleBoundedWith_sampleThen fun _ => (FreeM.costBoundedWith_pure _ _).mpr trivial)
    sampleQuery_oracleBounded sampleQuery_sampleBounded

/-- The simulated computation: the original sampling step, then the subroutine's. -/
theorem simulate_sampleQuery :
    simulate bitSub sampleQuery =
      sampleThen PUnit.unit fun _ => sampleThen PUnit.unit fun b => pure b :=
  rfl

/-- Both sampling steps occur on every path: the simulation is not `SampleBounded 1`, so the
bound of `sampleBounded_simulate` is attained here. -/
theorem not_simulate_sampleQuery_sampleBounded_one :
    ¬ SampleBounded 1 (simulate bitSub sampleQuery) := by
  rw [simulate_sampleQuery]
  intro h
  exact FreeM.not_costBoundedWith_zero_of_costly rfl
    ((FreeM.costBoundedWith_liftBind_of_costly rfl 0).mp h true)

/-! ### `ofCoins`: MAC forgers -/

/-- A toy MAC on `ZMod 2`: a uniform key `k`, the tag `k + m`, and verification by
recomputation. -/
noncomputable def toyMac : MACScheme (ZMod 2) (ZMod 2) (ZMod 2) where
  gen := Cslib.Probability.PMF.uniformOfFintype (ZMod 2)
  tag k m := PMF.pure (k + m)
  verify k m t := decide (t = k + m)

/-- Query `0`, which reveals the key `t = k`, and forge the tag `t + 1` on the fresh
message `1`. -/
noncomputable def macForger : MACForger (ZMod 2) (ZMod 2) Unit :=
  ⟨PMF.pure (), fun _ => query 0 fun t => done (1, t + 1)⟩

/-- The coin forger wins the coin game with probability `1`. -/
theorem macGame_macForger : macGame toyMac macForger = PMF.pure true := by
  simp only [macGame, toyMac, macForger, evalLog_pure_comp, run, queries, PMF.pure_bind,
    PMF.pure_map]
  refine (congrArg (PMF.bind _) (funext fun k => ?_)).trans (PMF.bind_const _ _)
  congr 1
  revert k
  decide

/-- **`ofCoins` computes the coin game**: the monadic game of the embedded forger is won with
probability `1`. -/
theorem mMacGame_ofCoins_macForger :
    mMacGame toyMac (MMACForger.ofCoins macForger) = PMF.pure true := by
  rw [mMacGame_ofCoins, macGame_macForger]

/-- The embedded forger's advantage is `1`. -/
theorem mMacAdvantage_ofCoins_macForger :
    mMacAdvantage toyMac (MMACForger.ofCoins macForger) = 1 := by
  rw [mMacAdvantage, mMacGame_ofCoins_macForger, winProb_pure]
  simp

/-- The embedded forger makes one tagging query, as the coin forger does. -/
theorem ofCoins_macForger_oracleBounded : (MMACForger.ofCoins macForger).OracleBounded 1 :=
  MMACForger.oracleBounded_ofCoins fun _ _ => trivial

/-- The query is counted: the embedded forger is not `OracleBounded 0`. -/
theorem not_ofCoins_macForger_oracleBounded_zero :
    ¬ (MMACForger.ofCoins macForger).OracleBounded 0 := by
  intro h
  simp only [MMACForger.OracleBounded, MMACForger.ofCoins] at h
  exact FreeM.not_costBoundedWith_zero_of_costly rfl
    ((FreeM.costBoundedWith_liftBind_of_free rfl 0).mp h ())

/-- The embedding samples the coins once. -/
theorem ofCoins_macForger_sampleBounded : (MMACForger.ofCoins macForger).SampleBounded 1 :=
  MMACForger.sampleBounded_ofCoins macForger

/-- The sampling family drawing a uniform element of `ZMod 2`. -/
noncomputable abbrev Offsets : SampleFam.{0} :=
  coinFam (Cslib.Probability.PMF.uniformOfFintype (ZMod 2))

/-- A monadic forger that queries `0`, learning `t = k`, then samples an offset `c` and forges the
tag `t + c` on the fresh message `1`; it is right exactly when `c = 1`. -/
noncomputable def guessForger : MMACForger Offsets (ZMod 2) (ZMod 2) :=
  ⟨queryThen 0 fun t => sampleThen PUnit.unit fun c => pure (1, t + c)⟩

/-- The sampling step after the query is part of the game: `guessForger` wins with probability
`1/2`. -/
theorem mMacAdvantage_guessForger : mMacAdvantage toyMac guessForger = 1 / 2 := by
  simp only [mMacAdvantage, mMacGame, toyMac, guessForger, mEvalLog_queryThen,
    mEvalLog_sampleThen, mEvalLog_pure, PMF.pure_bind, PMF.map_bind, PMF.pure_map,
    List.map_cons, List.map_nil, add_zero, add_right_inj, PMF.bind_const]
  change winProb ((Cslib.Probability.PMF.uniformOfFintype (ZMod 2)).map _) = 1 / 2
  rw [winProb_map_uniform]
  norm_num
  decide

/-! ### `ofCoins`: CPA adversaries -/

/-- A deterministic pad on `ZMod 2` with a reused key: `Enc_k(m) = k + m`. -/
noncomputable def padScheme : SymmEncScheme (ZMod 2) (ZMod 2) (ZMod 2) where
  gen := Cslib.Probability.PMF.uniformOfFintype (ZMod 2)
  enc k m := PMF.pure (k + m)
  dec k c := some (c - k)

/-- Query `Enc_k(0) = k`, challenge with `(0, 1)`, and unmask the challenge. -/
noncomputable def padAdv : CPAAdversary (ZMod 2) (ZMod 2) Unit :=
  ⟨PMF.pure (), fun _ => query 0 fun k => done ((0, 1), fun c => done (c - k == 1))⟩

/-- `padAdv` makes one encryption query. -/
theorem padAdv_queryBounded : padAdv.QueryBounded 1 := fun _ _ _ => trivial

/-- **`ofCoins` computes the coin experiment**: in the monadic CPA experiment the embedded
adversary always outputs the challenge bit. -/
theorem mCpaExp_ofCoins_padAdv (b : Bool) :
    mCpaExp padScheme (MCPAAdversary.ofCoins padAdv) b = PMF.pure b := by
  rw [mCpaExp_ofCoins]
  simp only [cpaExp, padScheme, padAdv, evalPMF_liftBind, evalPMF_pure', PMF.pure_bind]
  cases b <;> simp [show ((0 : ZMod 2) == 1) = false from by decide]

/-- The embedded adversary's monadic CPA advantage is `1/2`. -/
theorem mCpaAdvantage_ofCoins_padAdv :
    mCpaAdvantage padScheme (MCPAAdversary.ofCoins padAdv) = 1 / 2 := by
  rw [mCpaAdvantage, mCpaGame, guessAdvantage_bitGame, mCpaExp_ofCoins_padAdv,
    mCpaExp_ofCoins_padAdv]
  simp [advantage]

/-- The embedded adversary makes one encryption query and one sampling step. -/
theorem ofCoins_padAdv_bounded : (MCPAAdversary.ofCoins padAdv).OracleBounded 1 ∧
    (MCPAAdversary.ofCoins padAdv).SampleBounded 1 :=
  ⟨MCPAAdversary.oracleBounded_ofCoins padAdv_queryBounded,
    MCPAAdversary.sampleBounded_ofCoins padAdv⟩

end Cslib.Crypto.FrameworkTests.Monadic
