# IND-CPA security of dual-Regev encryption from decision LWE

Consider dual-Regev encryption with modulus $q = 2^w$, uniform binary secret $e \in \{0,1\}^m$ and LWE error distribution $\chi$ for $(x, x_0)$, with parameters indexed by $\kappa$. Suppose $m \ge n \log_2 q + \omega(\log \kappa)$ and decision LWE holds with $m + 1$ samples and error distribution $\chi$. Then the scheme is IND-CPA secure: for every probabilistic polynomial-time adversary the advantage in the chosen-plaintext experiment is negligible. Concretely, the advantage is at most twice the LWE advantage of an explicit reduction plus the statistical distance $\frac12\sqrt{q^{n}/2^m}$ between $(A, A^{\mathsf T} e)$ and a uniform pair.

## Proof sketch

By the leftover hash lemma the public key $(A, u)$ is statistically close to uniform. Stacking $u^{\mathsf T}$ on top of $A$ gives a uniform $(m+1) \times n$ matrix, and the ciphertext $(c_0, b)$ minus $\mu\,2^{w-1}$ is exactly an LWE sample for this matrix; replacing it by a uniform vector hides $\mu$.

## Depends on

- [Dual-Regev public-key encryption](dual-regev-encryption.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Leftover hash lemma](../../../randomness-extraction/leftover-hash-lemma.md)
- [Correctness of dual-Regev encryption](dual-regev-correctness.md)

## Sources

- Craig Gentry, Chris Peikert and Vinod Vaikuntanathan, "Trapdoors for Hard Lattices and New Cryptographic Constructions", Proceedings of the 40th Annual ACM Symposium on Theory of Computing, 2008.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
