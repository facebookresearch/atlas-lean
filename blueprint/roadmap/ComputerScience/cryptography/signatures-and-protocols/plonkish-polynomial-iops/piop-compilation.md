# Compiling polynomial IOPs with polynomial commitments into succinct arguments

Let $\Pi$ be a public-coin PIOP for $\mathcal{R}$ with knowledge soundness error $\epsilon$, and let $\mathsf{PC}$ be a polynomial commitment scheme for the same polynomial class that is binding and has knowledge-sound evaluation proofs (an extractor recovering the committed polynomial from accepting evaluation proofs). Replacing each oracle by a commitment and each query by an evaluation proof yields an interactive argument of knowledge for $\mathcal{R}$ with knowledge error $\epsilon+\mathrm{negl}(\lambda)$; if moreover the compiled argument has negligible state-restoration (for instance round-by-round) knowledge error, applying the Fiat–Shamir transform in the random oracle model yields a non-interactive argument of knowledge (a SNARK when $\mathsf{PC}$ has succinct commitments and evaluation proofs). Zero knowledge is preserved if $\Pi$ is honest-verifier zero knowledge with bounded query leakage and $\mathsf{PC}$ is hiding with zero-knowledge evaluation proofs.

## Proof sketch

The extractor uses the evaluation extractor of $\mathsf{PC}$ to obtain polynomials consistent with all answered queries; binding ensures these do not depend on the queries. The interaction then is a valid PIOP execution, so PIOP knowledge soundness applies. Fiat–Shamir soundness for the public-coin compiled argument follows in the random oracle model, with round-by-round or state-restoration analysis.

## Depends on

- [Polynomial interactive oracle proofs](polynomial-iop.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Security of the Fiat–Shamir transform](../zero-knowledge-and-arguments/security-of-the-fiatshamir-transform.md)
- [Succinct arguments and SNARKs](../zero-knowledge-and-arguments/succinct-arguments-and-snarks.md)
- [Knowledge soundness](../zero-knowledge-and-arguments/knowledge-soundness.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Sources

- Alessandro Chiesa, Yuncong Hu, Mary Maller, Pratyush Mishra, Psi Vesely, Nicholas Ward, "Marlin: Preprocessing zkSNARKs with Universal and Updatable SRS", EUROCRYPT (2020).
- Benedikt Bünz, Ben Fisch, Alan Szepieniec, "Transparent SNARKs from DARK Compilers", EUROCRYPT (2020), IACR ePrint 2019/1229.
