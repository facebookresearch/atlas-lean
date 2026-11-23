# Goldwasser–Micali encryption

The first public-key encryption scheme proved to hide *all* partial information about the plaintext
(Goldwasser and Micali, STOC 1982). Let $N = pq$ be a product of two distinct primes and let $y$ be a
quadratic non-residue modulo $N$ with Jacobi symbol $+1$. The public key is $(N, y)$ and the secret
key is $(p, q)$. A bit $b$ is encrypted, with a fresh uniform unit $x$ modulo $N$, as $x^2$ if $b = 0$
and as $y x^2$ if $b = 1$; a string is encrypted bit by bit. With the factorization, decryption tests
quadratic residuosity by Euler's criterion modulo $p$ and modulo $q$. Without it, deciding whether a
number with Jacobi symbol $+1$ is a square modulo $N$ is the quadratic residuosity problem.

Here the scheme is stated for a fixed modulus $N$. Correctness rests on Goldwasser and Micali's
Lemma 2 (Euler's criterion modulo $p$ and $q$, glued by the Chinese remainder theorem). The security
theorems are **per adversary**: an eavesdropper with advantage $\varepsilon$ against one-bit encryption
gives a distinguisher with advantage $2\varepsilon$ in the residuosity experiment
(Goldwasser–Micali's main theorem for one bit), every adversary computing a function of the plaintext
bit is matched by a simulator up to the residuosity advantage of one distinguisher built from it, and
for messages of $\ell$ bits the hybrid argument (their Theorem 3) bounds a distinguisher's advantage by
the sum of $\ell$ residuosity advantages. Each reduction calls the adversary once, so the statements
carry over to efficient adversaries.

In this concrete model every function counts as an adversary, and an unbounded distinguisher can
decide residuosity: for any key whose $y$ is not a square, the hypothesis "every distinguisher has
residuosity advantage at most $\varepsilon$" forces $\varepsilon \ge 1$, and the scheme is not
indistinguishable for any error below $1$. An all-distinguisher form of security needs a
resource-bounded class of distinguishers.

In the STOC version, the partial-information security of Section 4.1 is proved for a uniformly
distributed message space and easily computable predicates; the general definition used here is
Goldreich's. Goldwasser and Micali also prove asymptotic statements under their quadratic
residuosity assumption on circuits, and the random self-reducibility of quadratic residuosity (their
Theorems 1 and 2). The residuosity experiment here is stated with $y x^2$ directly, so it needs
neither the uniformity of $y x^2$ among non-residues with Jacobi symbol $+1$ nor that $y$ have
Jacobi symbol $+1$.

## The scheme and its correctness

- [Goldwasser–Micali encryption of one bit](encrypt-bit.md)
- [Encryptions of $0$ are squares](is-square-encrypt-bit-false.md)
- [Encryptions of $1$ are non-squares](not-is-square-encrypt-bit-true.md)
- [Residuosity reveals the bit](is-square-encrypt-bit-iff.md)
- [Square units](is-square-units-iff.md)
- [Squares in a product](is-square-prod-iff.md)
- [Goldwasser–Micali's Lemma 2](is-square-iff-euler.md)
- [Goldwasser–Micali trapdoor decryption of one bit](decrypt-bit.md)
- [A valid Goldwasser–Micali key](is-key.md)
- [Correctness of Goldwasser–Micali encryption of one bit](decrypt-bit-encrypt-bit.md)
- [The Goldwasser–Micali scheme for one-bit messages](scheme.md)
- [Correctness of the Goldwasser–Micali scheme](scheme-correct.md)

## Security from the residuosity experiment, per adversary

- [The residuosity experiment](qr-exp.md)
- [Residuosity advantage](qr-advantage.md)
- [The reduction from Goldwasser–Micali to the residuosity experiment](reduction.md)
- [The reduction for one key and one coin](inner-identity.md)
- [Goldwasser–Micali's main theorem for one bit, per adversary](pub-cpa-advantage-eq-qr-advantage.md)
- [Residuosity bounds transfer to Goldwasser–Micali, per adversary](pub-cpa-advantage-le.md)
- [Distinguishing Goldwasser–Micali ciphertexts is deciding residuosity](ind-exp-scheme.md)
- [Semantic security of Goldwasser–Micali for one bit, per adversary](win-prob-ss-real-le-qr-advantage.md)

## Messages of several bits

- [Bitwise Goldwasser–Micali encryption](encrypt-vec.md)
- [The Goldwasser–Micali scheme for $\ell$-bit messages](scheme-vec.md)
- [Correctness of bitwise Goldwasser–Micali encryption](scheme-vec-correct.md)
- [Resampling one coordinate of a uniform vector](uniform-map-update.md)
- [Encrypting with updated randomness](encrypt-vec-update.md)
- [The $\ell$-bit experiment with one coordinate resampled](ind-exp-scheme-vec-eq.md)
- [The hybrid reduction at position $j$](hybrid-reduction.md)
- [The coins of the hybrid reduction](hybrid-coins.md)
- [One hybrid step](ind-exp-scheme-vec-hybrid.md)
- [The $j$-th hybrid message](hybrid-msg.md)
- [The hybrid argument for bitwise Goldwasser–Micali encryption](ind-advantage-scheme-vec-le.md)
- [Bitwise Goldwasser–Micali encryption loses a factor $\ell$](ind-advantage-scheme-vec-le-mul.md)

## Unbounded distinguishers

- [An unbounded distinguisher decides residuosity](one-le-of-forall-qr-advantage-le.md)
- [The one-bit Goldwasser–Micali scheme is not indistinguishable against unbounded distinguishers](not-ind-secure-scheme.md)

## Related topics

- [Semantic security and indistinguishability](../../security-games/semantic-security-and-indistinguishability/README.md):
  the definitions that Goldwasser and Micali introduced with this scheme.
- [Games and advantages](../../security-games/games-and-advantages/README.md): the averaging lemmas the reductions use.
- [RSA cryptosystem](../rsa-cryptosystem/README.md): a deterministic trapdoor-function scheme of the
  kind whose leakage of partial information motivated probabilistic encryption.
- [ElGamal encryption](../elgamal-encryption/README.md): a later probabilistic scheme, with security
  from the decisional Diffie–Hellman assumption.
- [Zero-knowledge proof of quadratic residuosity](../../signatures-and-protocols/zero-knowledge-proof-of-quadratic-residuosity/README.md):
  proving that a number is a quadratic residue without revealing a square root.
