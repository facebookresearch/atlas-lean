# Soundness of RGSep

Every judgment derivable in the RGSep proof system is semantically valid: a derived $C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$ guarantees that $C$, under interference within $\mathcal{R}$, never faults, changes shared state only within $\mathcal{G}$, and establishes $q$ on termination.

Use the judgments and rules of [RGSep proof rules](rgsep-proof-rules.md), with each atomic block annotated by the precise postcondition $Q$ of the atomic rule used for it, the [operational semantics of RGSep programs over structured heaps](operational-semantics-of-rgsep-programs.md) of an abstract separation algebra, and [semantic validity of RGSep judgments](semantic-validity-of-rgsep-judgments.md).

**Theorem (soundness).** If $\vdash C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$, then $\models C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$.

The theorem is stated for an arbitrary partial commutative cancellative monoid of heaps, so it applies to every heap model with these laws. The split of the heap into local, shared and environment parts serves only the proof; the source notes an erasure to a semantics without it.

## Depends on

- [RGSep proof rules](rgsep-proof-rules.md)
- [Semantic validity of RGSep judgments](semantic-validity-of-rgsep-judgments.md)

## Proof depends on

- [RGSep proof rules](rgsep-proof-rules.md)
- [Semantic validity of RGSep judgments](semantic-validity-of-rgsep-judgments.md)
- [Operational semantics of RGSep programs over structured heaps](operational-semantics-of-rgsep-programs.md)
- [RGSep assertions over local and shared state](rgsep-assertions-over-local-and-shared-state.md)

## Expansion

The proof is by induction on derivations. Its prerequisites, each a lemma about the operational semantics that the technical report proves in Coq, are: locality of reductions (a run on $\sigma_1 \uplus \sigma'$ either restricts to a run on $\sigma_1$ with $\sigma'$ framed off, or the run on $\sigma_1$ faults); monotonicity of the guarantee predicate in the state and in $G$, and of reductions in the rely; the decomposition of runs of atomic blocks and primitive commands into environment steps around one program step; and, for the parallel rule, that guarantees of $C_1$ under $\mathcal{R} \cup \mathcal{G}_2$ and of $C_2$ under $\mathcal{R} \cup \mathcal{G}_1$ give the guarantee $\mathcal{G}_1 \cup \mathcal{G}_2$ of $C_1 \parallel C_2$ under $\mathcal{R}$, with runs of the composition projecting to runs of the components. The atomic case uses precision of $Q$ to determine the split into local and shared heap and the stability facts for RGSep assertions; the frame rule for commands with atomic blocks is derived from the parallel rule with $\mathbf{skip}$. With procedures, validity is step-indexed and the theorem holds for every index.

## Sources

- V. Vafeiadis and M. Parkinson, "A marriage of rely/guarantee and separation logic", *CONCUR 2007 – Concurrency Theory*, LNCS 4703, Springer, 2007, pp. 256–271, <https://doi.org/10.1007/978-3-540-74407-8_18>, author copy <https://www.mpi-sws.org/~viktor/papers/concur2007-marriage.pdf>: Section 5, Theorem 2 (soundness), and Section 7 (reuse for other heap models).
- V. Vafeiadis and M. Parkinson, *A marriage of rely/guarantee and separation logic*, Technical Report UCAM-CL-TR-687, University of Cambridge Computer Laboratory, June 2007, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-687.pdf>: Section 5 (Lemmas 19–27, Definitions 28–30, Theorem 31 and its proof by cases).
