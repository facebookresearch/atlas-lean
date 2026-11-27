# Regev ciphertexts under a uniform public matrix are statistically hiding

Let $A$ be uniform in $\mathbb{Z}_q^{m \times (n+1)}$ with $q = 2^w$, and let the encryption coins $x \in \{0,1\}^m$ be uniform and independent for each ciphertext. Then for every adversary making $Q$ adaptive left-or-right encryption queries, the advantage of distinguishing encryptions of its left messages from encryptions of its right messages is at most

$$
Q \sqrt{\frac{q^{n+1}}{2^m}} .
$$

For a single challenge the bound is $\sqrt{q^{n+1}/2^m}$. Hence, if decision LWE holds for the key distribution, Regev's scheme with $m \ge (n+1)\log_2 q + \omega(\log \kappa)$ is IND-CPA secure.

## Proof sketch

The map $x \mapsto x^{\mathsf T}A$ is a universal hash family keyed by $A$; by the leftover hash lemma $(A, x^{\mathsf T}A)$ is within $\frac12\sqrt{q^{n+1}/2^m}$ of $(A, u)$, so each ciphertext is close to a uniform vector independent of the message. A hybrid over the $Q$ queries gives the bound; under LWE the real public key is indistinguishable from a uniform matrix.

## Depends on

- [Regev's public-key encryption from learning with errors](../../hardness-assumptions/regev-s-public-key-encryption-from-learning.md)
- [The CPA experiment](../../../symmetric-key/pseudorandom-functions/cpa-game.md)

## Proof depends on

- [Leftover hash lemma](../../../randomness-extraction/leftover-hash-lemma.md)
- [Hybrid argument](../../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", Journal of the ACM, 2009.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
