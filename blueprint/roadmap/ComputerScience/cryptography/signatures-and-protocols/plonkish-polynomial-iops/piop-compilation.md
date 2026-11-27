# Compiling polynomial IOPs with polynomial commitments into succinct arguments

Let $\Pi$ be a public-coin PIOP for $\mathcal{R}$ with negligible knowledge soundness error, and let $\mathsf{PC}$ be a polynomial commitment scheme for the same polynomial class that is binding and has knowledge-sound evaluation proofs (an extractor recovering the committed polynomial from accepting evaluation proofs; witness-extended emulation in Bünz–Fisch–Szepieniec). Replacing each oracle by a commitment and each query by an evaluation proof yields a public-coin interactive argument of knowledge for $\mathcal{R}$ (with witness-extended emulation when $\mathsf{PC}$ has it). Its communication is $O_\lambda(q)$ bits for $q$ the query complexity of $\Pi$ when $\mathsf{PC}$ is succinct, and for constant round complexity the Fiat–Shamir transform in the random oracle model makes it non-interactive, which is how Marlin obtains preprocessing zkSNARKs. Zero knowledge is preserved: if $\mathsf{PC}$ is hiding and $\Pi$ is zero knowledge with query bound $q$ and a polynomial-time query checker, the argument is zero knowledge (Marlin); if $\mathsf{PC}$ is hiding with an honest-verifier zero-knowledge evaluation protocol, honest-verifier zero knowledge of $\Pi$ is preserved (Bünz–Fisch–Szepieniec).

## Proof sketch

The extractor uses the evaluation extractor of $\mathsf{PC}$ to obtain polynomials consistent with all answered queries; binding ensures these do not depend on the queries. The interaction then is a valid PIOP execution, so PIOP knowledge soundness applies; negligible knowledge error of $\Pi$ keeps the combined error negligible.

## Depends on

- [Polynomial interactive oracle proofs](polynomial-iop.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Security of the Fiat–Shamir transform](../zero-knowledge-and-arguments/security-of-the-fiatshamir-transform.md)
- [Succinct arguments and SNARKs](../zero-knowledge-and-arguments/succinct-arguments-and-snarks.md)
- [Knowledge soundness](../zero-knowledge-and-arguments/knowledge-soundness.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Sources

- Alessandro Chiesa, Yuncong Hu, Mary Maller, Pratyush Mishra, Psi Vesely, Nicholas Ward, "Marlin: Preprocessing zkSNARKs with Universal and Updatable SRS", EUROCRYPT (2020), IACR ePrint 2019/1047 (Theorems 8.1, 8.3 and 8.4).
- Benedikt Bünz, Ben Fisch, Alan Szepieniec, "Transparent SNARKs from DARK Compilers", EUROCRYPT (2020), IACR ePrint 2019/1229 (Theorem 4).
