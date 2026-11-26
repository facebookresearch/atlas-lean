# Trapdoor permutations

A **key-indexed trapdoor permutation scheme** is a trapdoor function scheme in which the domain and codomain coincide at every generated public key. Fix a positive security parameter $\lambda$, given in unary. Setup draws a public system parameter $\Lambda$ and key generation, given $(1^\lambda,\Lambda)$, draws a pair $(pk,sk)$. These are the generators’ own distributions, not uniform draws over the sets of legal parameters or keys.

Write $X$ and $Y$ for the finite bitstring spaces at $(1^\lambda,\Lambda,pk)$. Both have uniform polynomial-time membership tests. One polynomial in $\lambda$ bounds the lengths of every generated $\Lambda$, both keys, and every element of either space. The domain $X$ is nonempty and has an exact uniform sampler given the public context. Evaluation $F$ and inversion $I$ are **deterministic** polynomial-time maps. With $(1^\lambda,\Lambda)$ understood, $F(pk,\cdot)$ takes $X$ to $Y$, $I(sk,\cdot)$ takes $Y$ to $X$, and

$$
I(sk,F(pk,x))=x \qquad (x\in X).
$$

These conditions apply to every system parameter in the support of setup and every matching key pair in the conditional key law’s support. They imply injectivity but do not require surjectivity onto a larger $Y$. If $Y=X$, injectivity on the finite set implies surjectivity, so $I(sk,\cdot)$ is also a right inverse there.

**[One-wayness](is-one-way.md)** is a separate assumption. In the [keyed experiment](one-way-game.md), after setup and key generation, draw $x$ uniformly from this key’s $X$. The adversary gets $(1^\lambda,\Lambda,pk,F(pk,x))$ and independent fair bits, not $sk$. For every single strict polynomial-time adversary and every polynomial coin budget $q(\lambda)$, its probability of outputting the exact string $x$ must be negligible in $\lambda$. The [unkeyed one-way function experiment](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md) instead samples a uniform $\lambda$-bit input and tests whether a decoded answer is *any* preimage. It does not sample and reveal a public key.

**Sampling convention.** Here setup, key generation and domain sampling are each a single polynomial-time map of their inputs and a fresh fair bitstring of a fixed polynomial length in $\lambda$. Their output laws must agree *exactly* with the specified laws. This is stricter than Boneh–Shoup’s Definition 2.8, which permits a negligible probability of exceeding a polynomial time bound. For example, a uniform draw from three elements can be made by rejection sampling, but cannot be the image of a fixed number $m$ of fair bits: three does not divide $2^m$. Approximating the uniform law with a bounded sampler is not exact sampling.

**Source convention and RSA.** Boneh–Shoup’s Definition 10.2 fixes $X,Y$; Definition 10.4 allows them to depend on $(\lambda,\Lambda)$, **not** on the subsequently generated $pk$. In §10.3 their RSA example uses **all** residues $\mathbb Z/N\mathbb Z$, including zero and nonunits, not just the unit group. The modulus $N$ is generated with the keys. The authors explicitly note on p. 399 that this changes the space with $pk$ and falls outside their formal syntax. For a lawful key, [RSA correctness](../rsa-cryptosystem/decrypt-encrypt.md) and [bijectivity](../rsa-cryptosystem/encrypt-bijective.md) give the algebraic permutation on those residues. The RSA assumption (Game 10.3 and Definition 10.5) concerns recovery of a uniformly drawn residue for the specified random modulus and exponent parameters; the algebraic identities do not prove it. Nor do they supply an exact bounded-coin sampler for an odd modulus.

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, September 2017, §§2.4.2–2.4.3 and 10.2–10.3, especially Definitions 10.2–10.5, Games 10.2–10.3 and Theorem 10.1, pp. 395–401. <https://toc.cryptobook.us/>
