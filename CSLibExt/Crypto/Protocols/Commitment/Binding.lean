/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Advantage
public import Cslib.Crypto.Protocols.Commitment.Basic

/-!
# The computational binding game for keyed commitment schemes

A keyed commitment scheme is a family `S : K → Scheme M C O` of CSLib commitment schemes
(`Cslib.Crypto.Protocols.Commitment.Scheme`) together with a key-generation distribution
`gen : PMF K`. In the binding experiment (Katz and Lindell, Section 5.6.5) a key `k ← gen` is
published, and the adversary, from `k` and its coins, outputs a commitment with two openings; it
wins when both openings are accepted by `S k` and open to different messages.

As in `CSLibExt.Crypto.Framework.Games`, the adversary carries its coins as an arbitrary
distribution `coins : PMF R` (`BindingAdversary`), and is otherwise a deterministic function of
the key and the coins; neither the coins nor the key need be uniform or finitely supported.

* `BindingAdversary`, `BindingWin`, `bindingGame`, `bindingAdvantage`: the experiment.
* Reductions that reuse the adversary's coins and the same key distribution bound
  `bindingAdvantage` with `Cslib.Crypto.Framework.winProb_bind_map_mono`: if one outcome map
  implies another on every key in the support of the key distribution, the success probability
  can only grow. `winProb_bind_map_mono` in this namespace is a deprecated alias of it.

Pedersen commitments (`CSLibExt.Crypto.Protocols.Commitment.Pedersen`) and hash commitments
(`CSLibExt.Crypto.Protocols.Commitment.HashCommitment`) are both instances.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 5.6.5 (commitment schemes: hiding and binding).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.Commitment

open Cslib.Crypto.Framework

/-- A binding adversary against a keyed commitment scheme with keys in `K`: with coins
`r ← coins`, from the key it outputs a commitment and two openings `(m, o)` and `(m', o')`. -/
structure BindingAdversary (K M C O R : Type*) where
  /-- The distribution of the adversary's random coins. -/
  coins : PMF R
  /-- The adversary, as a function of the key and its coins. -/
  run : K → R → C × (M × O) × (M × O)

variable {K M C O R : Type*}

/-- The adversary wins against the scheme `S` on output `(c, (m, o), (m', o'))` when both
openings are accepted and `m ≠ m'`. -/
def BindingWin (S : Scheme M C O) (out : C × (M × O) × (M × O)) : Prop :=
  S.Accepts out.2.1.1 out.1 out.2.1.2 ∧ S.Accepts out.2.2.1 out.1 out.2.2.2 ∧
    out.2.1.1 ≠ out.2.2.1

instance [DecidableEq M] (S : Scheme M C O) (out : C × (M × O) × (M × O)) :
    Decidable (BindingWin S out) := by
  unfold BindingWin Scheme.Accepts; infer_instance

variable [DecidableEq M]

/-- **The binding experiment** for the keyed commitment scheme `S` with key generation `gen`
(Katz and Lindell, Section 5.6.5): `k ← gen`, `r ← A.coins`, and the experiment outputs `1` when
`A.run k r` opens one commitment of `S k` to two different messages. -/
noncomputable def bindingGame (gen : PMF K) (S : K → Scheme M C O)
    (A : BindingAdversary K M C O R) : PMF Bool :=
  gen.bind fun k => A.coins.map fun r => decide (BindingWin (S k) (A.run k r))

/-- The binding advantage: the success probability in `bindingGame`. -/
noncomputable def bindingAdvantage (gen : PMF K) (S : K → Scheme M C O)
    (A : BindingAdversary K M C O R) : ℝ :=
  winProb (bindingGame gen S A)

@[deprecated (since := "2026-11-13")]
alias winProb_bind_map_mono := Cslib.Crypto.Framework.winProb_bind_map_mono

end Cslib.Crypto.Protocols.Commitment
