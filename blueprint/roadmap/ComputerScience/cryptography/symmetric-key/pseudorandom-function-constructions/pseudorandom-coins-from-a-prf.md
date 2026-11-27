# Pseudorandom coins derived from a pseudorandom function

Let $F$ be a PRF with $N$-bit keys, inputs and outputs. For request words $w$ of length less than $N$, pad $w$ prefix-freely to $N$ bits and output the first $\ell \le N$ bits of $F(k, \mathrm{pad}(w))$ as the coins for $w$. Then any efficient experiment in which a stateless algorithm derives its coins for request $w$ in this way is indistinguishable from the same experiment where each distinct request receives independent uniform coins and repeated requests receive the same coins.

## Proof sketch

Distinct requests pad to distinct PRF inputs; replace $F(k, \cdot)$ by a lazily sampled random function, whose answers on distinct inputs are independent and uniform.

## Depends on

- [Asymptotic PRF security relative to a class of distinguishers](../pseudorandom-functions/prfsecure.md)

## Proof depends on

- [Lazy random function](../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/lazy-rf.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- O. Goldreich, "Two Remarks Concerning the Goldwasser-Micali-Rivest Signature Scheme", Advances in Cryptology (CRYPTO 1986), LNCS 263, 1987.
