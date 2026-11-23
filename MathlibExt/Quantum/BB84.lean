/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod

/-!
# BB84 intercept-resend error rate

In BB84, Alice sends the bit `a` encoded in the basis `ba` (`false` = Z, `true` = X); qubits
and channel are ideal and noiseless. In an intercept-resend attack, Eve measures the qubit in a
basis `be` and resends her result `e` encoded in `be`; Bob then measures in a basis `bb` and
obtains `r`. Measuring a basis state in its own basis returns its bit, and measuring it in the
other basis returns a fair coin. So `e = a` when `be = ba` and `e` is Eve's coin `ce` otherwise
(`bb84EveResult`), and `r = e` when `bb = be` and `r` is Bob's coin `cb` otherwise
(`bb84BobResult`). A round is sifted when `bb = ba`, and it has an error when it is sifted and
`r ≠ a`.

Eve's coin never matters in a sifted round. If `be = ba`, Bob measures Eve's copy of `a` in its own
basis and gets `r = a`. If `be ≠ ba`, then also `bb ≠ be`, so `r = cb`. The sifted error event is
therefore `bb = ba ∧ be ≠ ba ∧ cb ≠ a` (`bb84Error`, and `bb84Error_eq` for the derivation), a
function of the five independent fair bits `(a, cb, ba, be, bb)`. Of their 32 equally likely
values, 16 are sifted and 4 of those have an error, so the attack causes errors in `1/4` of the
sifted rounds.

## References

* C. H. Bennett and G. Brassard, *Quantum cryptography: Public key distribution and coin tossing*,
  Proceedings of the International Conference on Computers, Systems and Signal Processing,
  Bangalore, 1984; reprinted in Theoret. Comput. Sci. 560 (2014). Section II: a state of one basis
  gives a random result when measured in the conjugate basis. Section III: the protocol, and an
  eavesdropper who measures and resends every photon in one fixed basis causes disagreements in
  `1/4` of the photons later measured in their original basis.
* N. Gisin, G. Ribordy, W. Tittel and H. Zbinden, *Quantum cryptography*, Rev. Mod. Phys. 74
  (2002). Section II.C: the intercept-resend strategy modeled here, with Eve choosing her basis at
  random, causes about 25% errors in the sifted key.
-/

@[expose] public section

/-- Eve's result in an intercept-resend attack on BB84: measuring Alice's bit `a`, sent in the
basis `ba`, in the basis `be` returns `a` when the bases agree and Eve's fair coin `ce`
otherwise. -/
def bb84EveResult (a ba be ce : Bool) : Bool :=
  if be = ba then a else ce

/-- Bob's result in an intercept-resend attack on BB84: measuring Eve's resent bit `e`, encoded in
the basis `be`, in the basis `bb` returns `e` when the bases agree and Bob's fair coin `cb`
otherwise. -/
def bb84BobResult (e be bb cb : Bool) : Bool :=
  if bb = be then e else cb

/-- The BB84 intercept-resend error event in closed form, for Alice's bit `a`, Bob's coin `cb`,
and the bases `ba`, `be`, `bb` of Alice, Eve and Bob: the round is sifted (`bb = ba`), Eve measured
in the other basis (`be ≠ ba`), and Bob's coin differs from Alice's bit. By `bb84Error_eq` this is
the event that the round is sifted and Bob's result differs from `a`, for every value of Eve's
coin. -/
def bb84Error (a cb : Bool) (ba be bb : Bool) : Bool :=
  (bb == ba) && (be != ba) && (cb != a)

/-- The closed form `bb84Error` is the sifted error event of the intercept-resend model: the round
is sifted and Bob's result, obtained from Eve's resent result, differs from Alice's bit, whatever
Eve's coin `ce`. -/
theorem bb84Error_eq (a cb ba be bb ce : Bool) :
    bb84Error a cb ba be bb =
      ((bb == ba) && (bb84BobResult (bb84EveResult a ba be ce) be bb cb != a)) := by
  revert a cb ba be bb ce
  decide

/-- Of the 32 equally likely values of `(a, cb, ba, be, bb)`, exactly 4 are sifted rounds
(`bb = ba`) with an error. -/
theorem bb84_sifted_errors :
    (Finset.univ.filter (fun p : Bool × Bool × Bool × Bool × Bool =>
      bb84Error p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
        && (p.2.2.2.2 == p.2.2.1))).card = 4 := by
  decide

/-- Exactly 16 of the 32 values of `(a, cb, ba, be, bb)` are sifted rounds (`bb = ba`). With
`bb84_sifted_errors`, the sifted error rate is `4 / 16 = 1 / 4`. -/
theorem bb84_sifted_total :
    (Finset.univ.filter (fun p : Bool × Bool × Bool × Bool × Bool =>
      p.2.2.2.2 == p.2.2.1)).card = 16 := by
  decide

/-- No error occurs when Eve measures in Alice's basis, whatever Bob's basis and coin. -/
theorem bb84_no_error_when_eve_correct (a cb : Bool) (ba bb : Bool) :
    bb84Error a cb ba ba bb = false := by
  simp [bb84Error]

end
