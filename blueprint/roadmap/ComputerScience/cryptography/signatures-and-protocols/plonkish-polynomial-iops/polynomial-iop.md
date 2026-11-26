# Polynomial interactive oracle proofs

A *polynomial interactive oracle proof (PIOP)* over a field $\mathbb{F}$ for a relation $\mathcal{R}$ is a public-coin interactive protocol in which, in each round, the prover sends oracles to polynomials $f\in\mathbb{F}[X]$ of degree at most a bound $D$ (or multilinear polynomials in $\mathbb{F}[X_1,\dots,X_s]$), and the verifier, after sending random challenges, may query these oracles at points of its choice and finally accepts or rejects. Soundness error $\epsilon$ means that for $x$ with no witness, every (unbounded) prover strategy restricted to sending polynomials of the declared degrees makes the verifier accept with probability at most $\epsilon$; knowledge soundness requires a witness to be extractable from the sent polynomials.

## Depends on

- [Interactive arguments](../zero-knowledge-and-arguments/interactive-arguments.md)

## Sources

- Alessandro Chiesa, Yuncong Hu, Mary Maller, Pratyush Mishra, Psi Vesely, Nicholas Ward, "Marlin: Preprocessing zkSNARKs with Universal and Updatable SRS", EUROCRYPT (2020).
- Benedikt Bünz, Ben Fisch, Alan Szepieniec, "Transparent SNARKs from DARK Compilers", EUROCRYPT (2020), IACR ePrint 2019/1229.
