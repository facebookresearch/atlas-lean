# Fiat–Shamir with hints

A *Sigma protocol with hints* is a three-move public-coin protocol $(\mathsf{com},\mathsf{ch},\mathsf{resp})$ for a relation $\mathcal{R}$ together with a hint distribution $\mathcal{H}(x)$ such that (i) special soundness holds as usual, and (ii) there is an efficient simulator that, given the statement $x$ and an independent sample $h\leftarrow\mathcal{H}(x)$ (the hint), outputs transcripts distributed as honest ones. The *Fiat–Shamir with hints* framework proves EUF-CMA security of the resulting signature scheme in the random oracle model from the hardness of the underlying problem *in the presence of polynomially many hints* (a non-interactive assumption), capturing protocols such as SQIsign whose transcripts cannot be simulated from the statement alone.

## Depends on

- [Security of the Fiat–Shamir transform](../../../signatures-and-protocols/zero-knowledge-and-arguments/security-of-the-fiatshamir-transform.md)
- [Zero-knowledge interactive proofs](../../../signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)

## Sources

- Marius A. Aardal, Andrea Basso, Luca De Feo, Sikhar Patranabis, Benjamin Wesolowski, "A Complete Security Proof of SQIsign", CRYPTO (2025), IACR ePrint 2025/379.
