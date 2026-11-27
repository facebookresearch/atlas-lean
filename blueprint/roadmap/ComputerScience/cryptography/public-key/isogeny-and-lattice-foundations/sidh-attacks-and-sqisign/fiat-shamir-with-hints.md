# Fiat–Shamir with hints

Let $\Sigma$ be a three-move public-coin protocol $(\mathsf{com},\mathsf{ch},\mathsf{resp})$ for a relation $\mathcal{R}$ with challenge space $\mathcal{C}$, and let $\mathcal{H}=\{\mathcal{H}_x\}$ be a hint distribution, so that $(\mathcal{R},\mathcal{H})$ is a *relation with hints*. Suppose that (i) $\Sigma$ is special sound with respect to a *soundness relation* $\tilde{\mathcal{R}}$ compatible with $\mathcal{R}$ (same statement distribution, possibly different witnesses); (ii) $\Sigma$ is *$\mathcal{H}$-hint-assisted weak honest-verifier zero-knowledge*: an efficient simulator given $x$ and fresh hints $h_i\leftarrow\mathcal{H}_x$ outputs polynomially many transcripts, jointly computationally indistinguishable from as many honest ones; (iii) commitments have high min-entropy (negligible maximal probability); and (iv) $|\mathcal{C}|$ is superpolynomial. The *Fiat–Shamir with hints* theorem states that the resulting signature scheme is EUF-CMA secure in the random oracle model if $(\tilde{\mathcal{R}},\mathcal{H})$ is a hard relation with hints, that is, hard to solve given polynomially many hints (a non-interactive assumption); the advantage bound carries, besides the hint-relation and simulation advantages, the terms $1/|\mathcal{C}|$ and $(q+s+1)s$ times the maximal commitment probability, for $q$ random-oracle and $s$ signing queries. This captures protocols such as SQIsign, whose transcripts cannot be simulated from the statement alone and which are special sound only with respect to a weaker soundness relation (for SQIsign, the relation of knowing one non-scalar endomorphism of the public curve) rather than the original key relation.

## Depends on

- [Security of the Fiat–Shamir transform](../../../signatures-and-protocols/zero-knowledge-and-arguments/security-of-the-fiatshamir-transform.md)
- [Zero-knowledge interactive proofs](../../../signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)

## Sources

- Marius A. Aardal, Andrea Basso, Luca De Feo, Sikhar Patranabis, Benjamin Wesolowski, "A Complete Security Proof of SQIsign", CRYPTO (2025), IACR ePrint 2025/379, Section 3 (Definitions 3.2 to 3.4 and Theorem 1) and Section 4.2.
