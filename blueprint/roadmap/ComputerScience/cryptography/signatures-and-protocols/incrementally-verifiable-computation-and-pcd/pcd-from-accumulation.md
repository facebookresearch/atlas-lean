# Proof-carrying data from NARKs with split accumulation

Let $(\mathsf{G},\mathsf{P},\mathsf{V})$ be a NARK for circuit satisfiability with a split accumulation scheme $\mathsf{AS}$ for its verifier. For an index of size at most $N$ and the accumulation of $m$ instance-proof pairs and accumulators, let $v^*(\lambda,m,N,\ell)$ be the size of the accumulation verifier circuit when each of its instances consists of the accumulator verification key, an accumulator instance and $\ell$ further bits, and suppose the accumulator instance has size bounded by a function of $\lambda, m, N$ alone, independent of the instance size. If $\mathsf{AS}$ is sublinear, that is, $v^*(\lambda,m,N,\ell) = O(N^{1-\epsilon}\cdot\alpha(\lambda,m,\ell))$ for some $\epsilon \in (0,1)$ and some polynomial $\alpha$, then a polynomial-time transformation of the NARK and $\mathsf{AS}$ gives a PCD scheme for constant-depth compliance predicates, and hence IVC (knowledge sound in the standard model, given knowledge soundness of the NARK and of $\mathsf{AS}$), in which each vertex proves only that the compliance predicate $\varphi$ holds and that the accumulation verifier accepted the accumulation of the incoming proofs and accumulators into a new accumulator; the final verifier runs the NARK verifier and the decider once. If moreover $\varphi$ has size $f = \omega(\alpha(\lambda,m,\ell)^{1/\epsilon})$, each step proves a circuit of size $f + o(f)$.

## Proof sketch

Each vertex runs $\mathsf{AS.P}$ on the incoming NARK instances and accumulators, then produces a NARK proof for the circuit "the compliance predicate holds and $\mathsf{AS.V}$ accepts". Because the accumulation verifier is sublinear in the index size, the recursive circuit does not blow up: for large enough $\varphi$ its size is $f + o(f)$. Knowledge soundness follows by recursive extraction: from an accepted proof and a valid final accumulator, accumulation soundness yields valid incoming accumulators and NARK proofs, whose extractor yields the local data; constant depth keeps extraction polynomial.

## Depends on

- [Split accumulation and NARKs with accumulation](split-accumulation.md)
- [Proof-carrying data for a compliance predicate](pcd-scheme.md)
- [Incrementally verifiable computation scheme for an iterated function](ivc-scheme.md)
- [Knowledge soundness](../zero-knowledge-and-arguments/knowledge-soundness.md)

## Proof depends on

- [Size bound for recursively composed knowledge extractors](recursive-extraction-blowup.md)

## Sources

- Benedikt Bünz, Alessandro Chiesa, William Lin, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data without Succinct Arguments", CRYPTO (2021), IACR ePrint 2020/1618 (Definition 5.2, Theorem 5.3, Remark 5.4).
- Benedikt Bünz, Alessandro Chiesa, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data from Accumulation Schemes", TCC (2020), IACR ePrint 2020/499.
