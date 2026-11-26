# IVC and constant-depth PCD from knowledge-extractable SNARKs

Assume a preprocessing SNARK for NP (circuit satisfiability) with succinct verification and a knowledge extractor of polynomial size for every polynomial-size prover. Then: (i) for every polynomial-time compliance predicate $\varphi$ there is a PCD system for $\varphi$ that is knowledge sound for transcripts of constant depth; (ii) for every polynomial-time step function $F$ there is an IVC scheme for $F$ supporting $\mathrm{poly}(\lambda)$ steps, whose proof size and verification time are $\mathrm{poly}(\lambda,|F|)$, obtained by aggregating step proofs along a tree of constant depth and polynomial arity (Valiant's tree construction).

## Proof sketch

At each vertex the prover proves, with the SNARK, the statement "the local predicate holds and each incoming proof is accepted by the SNARK verifier"; succinct verification keeps this circuit of size $\mathrm{poly}(\lambda,|\varphi|)$ independent of depth. Knowledge soundness follows by recursive extraction, which by the extractor blow-up lemma stays polynomial for constant depth. For IVC, steps are arranged as leaves of a tree of depth $O(1)$ with arity $\lambda^{O(1)}$, giving polynomially many steps while extraction depth stays constant.

## Depends on

- [Incrementally verifiable computation scheme for an iterated function](ivc-scheme.md)
- [Proof-carrying data for a compliance predicate](pcd-scheme.md)
- [Succinct arguments and SNARKs](../zero-knowledge-and-arguments/succinct-arguments-and-snarks.md)

## Proof depends on

- [Size bound for recursively composed knowledge extractors](recursive-extraction-blowup.md)

## Sources

- Paul Valiant, "Incrementally Verifiable Computation or Proofs of Knowledge Imply Time/Space Efficiency", TCC (2008).
- Nir Bitansky, Ran Canetti, Alessandro Chiesa, Eran Tromer, "Recursive Composition and Bootstrapping for SNARKs and Proof-Carrying Data", STOC (2013).
