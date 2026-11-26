/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.DHSecurity

/-!
# Man-in-the-middle attack on unauthenticated Diffie–Hellman key agreement

In Diffie–Hellman key agreement (`DHSecurity.transcript`, `DHSecurity.aliceKey`,
`DHSecurity.bobKey`) neither party authenticates its message. An active adversary with exponents
`a'` and `b'` blocks Alice's message `g ^ a` and Bob's message `g ^ b` and sends the messages of
its own transcript `transcript g a' b'` instead: Bob receives `g ^ a'` and Alice receives `g ^ b'`
(Boneh and Shoup, Section 10.7 and Fig. 10.4).

* `aliceKey_bobKey_man_in_the_middle`: the key Alice then outputs is the key Bob would output with
  secret `b'` on Alice's message, and the key Bob outputs is the key Alice would output with
  secret `a'` on Bob's message; the adversary computes both from its exponents and the two
  messages it intercepted. Alice's exchange is thus an honest exchange with secrets `a` and `b'`,
  and Bob's one with secrets `a'` and `b`, and each half of the statement is
  `aliceKey_eq_bobKey` for one of them.

Boneh and Shoup conclude that the adversary, holding both keys, can decrypt what each party
encrypts and re-encrypt it for the other without either party noticing. That consequence concerns
the traffic after the key exchange, which this file does not model.

## References

* D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017,
  Sections 10.4.1 and 10.7, Fig. 10.4.
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.DHSecurity

variable {G : Type*} [CommGroup G] {q : ℕ} (g : G)

/-- **Man-in-the-middle attack on unauthenticated Diffie–Hellman key agreement** (Boneh and
Shoup, Section 10.7 and Fig. 10.4). Let $G$ be a commutative group, $g \in G$ and $q$ a natural
number, with exponents in $\mathbb{Z}/q$ read as in `transcript`. Alice, with secret $a$, sends
$g^a$ and Bob, with secret $b$, sends $g^b$. An adversary with exponents $a'$ and $b'$ intercepts
both messages and replaces them with those of its own transcript, so that Bob receives $g^{a'}$
and Alice receives $g^{b'}$. Then the key $(g^{b'})^a$ that Alice derives equals $(g^a)^{b'}$,
which the adversary computes from $b'$ and Alice's message, and the key $(g^{a'})^b$ that Bob
derives equals $(g^b)^{a'}$, which it computes from $a'$ and Bob's message. -/
theorem aliceKey_bobKey_man_in_the_middle (a b a' b' : ZMod q) :
    aliceKey a (transcript g a' b').2 = bobKey b' (transcript g a b).1 ∧
      bobKey b (transcript g a' b').1 = aliceKey a' (transcript g a b).2 :=
  ⟨aliceKey_eq_bobKey g a b', (aliceKey_eq_bobKey g a' b).symm⟩

end Cslib.Crypto.PublicKey.DHSecurity
