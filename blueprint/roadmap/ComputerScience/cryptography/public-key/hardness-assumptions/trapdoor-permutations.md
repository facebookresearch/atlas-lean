# Trapdoor permutations

A **key-indexed trapdoor permutation scheme** is a trapdoor function scheme whose domain and codomain coincide for every generated public context. One-wayness is a separate property. The key-indexed version allows the finite sets to depend on the public key, as well as on the security and system parameters.

For each positive security parameter $\lambda$, given in unary, a randomised setup algorithm draws a public system parameter $\Lambda$. Given $(1^\lambda,\Lambda)$, a randomised generator draws a matching pair $(pk,sk)$. These are the algorithms’ output distributions, not uniform draws over their supports. At each possible $(\lambda,\Lambda,pk)$ there are finite bitstring spaces $X,Y$ with deterministic efficient membership tests. One polynomial in $\lambda$ bounds the lengths of every generated $\Lambda$, both keys, and every element of either space. Given only the public context, an efficient randomised sampler outputs an **exactly uniform** element of the nonempty $X$.

The efficient maps $F$ and $I$ are **deterministic**. With $(1^\lambda,\Lambda)$ understood, $F(pk,\cdot)$ maps $X$ to $Y$, $I(sk,\cdot)$ maps all of $Y$ to $X$, and

$$
I(sk,F(pk,x))=x \qquad (x\in X).
$$

This holds for every $\Lambda$ in the support of setup and every pair in the support of key generation conditional on that $\Lambda$. A left inverse implies injectivity but not surjectivity onto a larger $Y$. When $Y=X$, [finiteness gives bijectivity and the other inverse law](bij-on-and-right-inv-on.md).

**Efficiency and exact sampling.** In Boneh–Shoup’s convention (Definitions 2.8–2.9), each randomised algorithm is a single machine using independent fair bits. It halts almost surely with the specified output law. There are a polynomial time bound $t$ and a negligible function $\epsilon$, independent of the input, such that for every positive $\lambda$ and every permitted input of polynomially bounded length at that parameter, the probability that this very execution takes more than $t(\lambda)$ steps is at most $\epsilon(\lambda)$. Bounding the number of bits read is not a substitute for bounding the running time. Nor is a negligible *time overrun* an error in the output law.

For example, a cycle on three points with constant keys has an exact sampler: assign three bit-pairs to the three points and repeat after the fourth pair. Its probability of needing more than $k$ pairs is $4^{-k}$; its running time is polynomial in $\lambda$ except with negligible probability. In contrast, a [bounded-coin permutation scheme](is-bounded-coin-permutation-scheme.md) requires a strictly polynomial-time sampler using a fixed polynomial number of fair bits. Its [domain cardinality divides the number of possible tapes](card-domain-dvd.md), which rules out three points. The cycle illustrates sampling and correctness, not one-wayness.

**One-wayness.** After setup and key generation draw $x$ uniformly from this key’s $X$. Give the adversary $(1^\lambda,\Lambda,pk,F(pk,x))$, but not $sk$. For every uniform efficient adversary, the probability of returning the exact string $x$ must be negligible in $\lambda$, over setup, key generation, the conditional uniform draw and the adversary’s independent random bits. Efficiency here uses the authors’ negligible running-time-tail convention for adversaries (§2.4.3), not just a strict fixed coin budget. The [unkeyed one-way function experiment](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md) instead samples a uniform $\lambda$-bit input and tests whether a decoded answer is *any* preimage. It does not sample and reveal a public key.

**Source convention and RSA.** Boneh–Shoup’s Definition 10.2 fixes $X,Y$; Definition 10.4 allows them to depend on $(\lambda,\Lambda)$, **not** on the subsequently generated $pk$. In §10.3 their RSA example uses **all** residues $\mathbb Z/N\mathbb Z$, including zero and nonunits. The modulus $N$ is generated with the keys. The authors explicitly note on p. 399 that this changes the space with $pk$ and falls outside their formal syntax. For a lawful key, [RSA correctness](../rsa-cryptosystem/decrypt-encrypt.md) and [bijectivity](../rsa-cryptosystem/encrypt-bijective.md) give the algebraic permutation on those residues. The RSA assumption (Game 10.3 and Definition 10.5) concerns recovery of a uniform residue under the specified modulus distribution and exponent parameters; the algebraic identities do not prove it.

## Depends on

- [Data of a key-indexed trapdoor family](family.md)
- [Generated system parameters and matching keys](generated.md)
- [Trapdoor correctness at matching keys](correct-at.md)
- [Probabilistic Turing machines and their fair random tapes](../../security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md) (the machine model; the running-time convention above permits a negligible tail)
- [Negligible advantage](../../security-games/asymptotic-security/negligible-adv.md)

## Proof depends on

- [Finite-domain inverse laws](bij-on-and-right-inv-on.md) (for the bijectivity and right-inverse consequence)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, September 2017, §§2.4.2–2.4.3 (Definitions 2.8–2.9, p. 30, and 2.11, p. 33) and §§10.2–10.3 (Definitions 10.2–10.5, Games 10.2–10.3 and Theorem 10.1, pp. 395–401). <https://toc.cryptobook.us/>
