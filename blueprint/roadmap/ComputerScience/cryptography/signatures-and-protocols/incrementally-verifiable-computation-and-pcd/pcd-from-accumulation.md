# Proof-carrying data from NARKs with split accumulation

Let $(\mathsf{G},\mathsf{P},\mathsf{V})$ be a NARK for circuit satisfiability with a split accumulation scheme $\mathsf{AS}$ for its verifier, where the accumulation verifier circuit has size $\mathrm{poly}(\lambda)$ independent of the size of the NARK verifier's input. Then there is a PCD system (and hence IVC) for every polynomial-time compliance predicate, knowledge sound for constant-depth transcripts (in the standard model, given knowledge soundness of the NARK and of $\mathsf{AS}$), in which each vertex proves only that $\varphi$ holds and that the accumulation verifier accepted the folding of the incoming proofs into a new accumulator; the final verifier runs the decider once. Proof size is $\mathrm{poly}(\lambda)$ plus the size of one accumulator.

## Proof sketch

Each vertex runs $\mathsf{AS.P}$ on the incoming NARK instances and accumulators, then produces a NARK proof for the circuit "the compliance predicate holds and $\mathsf{AS.V}$ accepts". The recursion only checks the cheap accumulation verifier, so the circuit size does not grow. Knowledge soundness follows by recursive extraction: from an accepted proof and a valid final accumulator, accumulation soundness yields valid incoming accumulators and NARK proofs, whose extractor yields the local data; constant depth keeps extraction polynomial.

## Depends on

- [Split accumulation and NARKs with accumulation](split-accumulation.md)
- [Proof-carrying data for a compliance predicate](pcd-scheme.md)
- [Incrementally verifiable computation scheme for an iterated function](ivc-scheme.md)
- [Knowledge soundness](../zero-knowledge-and-arguments/knowledge-soundness.md)

## Proof depends on

- [Size bound for recursively composed knowledge extractors](recursive-extraction-blowup.md)

## Sources

- Benedikt Bünz, Alessandro Chiesa, William Lin, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data without Succinct Arguments", CRYPTO (2021), IACR ePrint 2020/1618.
- Benedikt Bünz, Alessandro Chiesa, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data from Accumulation Schemes", TCC (2020), IACR ePrint 2020/499.
