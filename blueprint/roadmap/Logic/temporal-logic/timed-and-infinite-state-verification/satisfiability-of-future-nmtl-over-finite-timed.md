# Satisfiability of future NMTL over finite timed words is undecidable

Adding the future abstract (call–return) timed modalities to future MTL makes satisfiability over finite timed words undecidable, although satisfiability of future MTL itself over finite timed words is decidable.

**Theorem (Bozzelli, Murano and Peron).** Satisfiability of future [NMTL](nested-metric-temporal-logic.md), interpreted in the pointwise semantics over finite timed words, is undecidable: there is no algorithm that decides, given a formula built with the timed until modalities $\widehat{\mathsf U}{}^g_I$ and $\widehat{\mathsf U}{}^a_I$ (and no since modalities), whether some nonempty finite timed word over the pushdown alphabet satisfies it at position $0$ (Theorem 6 of the source).

For comparison: over infinite timed words satisfiability of future MTL is already undecidable (Ouaknine and Worrell, FOSSACS 2006), MTL with past is undecidable, and over finite timed words future MTL is decidable (Ouaknine and Worrell, LMCS 2007); the fragment NMITL$_{(0,\infty)}$ is EXPTIME-complete.

## Depends on

- [Nested metric temporal logic](nested-metric-temporal-logic.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem for Minsky two-counter machines. A computation is encoded by a well-matched word $(\mathit{call}, \sigma) \cdot (\mathit{ret}, \sigma^R)$: the call part lists the configurations $\ell\, c_1^{n_1} c_2^{n_2}$ in order, and the return part repeats them in reverse, so that every call position is matched by the return carrying the same letter. A future NMTL formula $\varphi_M$ is built whose models have exactly such untimed words with a correct halting computation: a CaRet part (using the abstract next modality) enforces well-matching, an LTL part enforces consecution, initialization and halting, and a future MTL part with time constraints (strictly increasing timestamps, distance $1$ between the labels of adjacent configurations) enforces the increment and decrement requirements, comparing counter blocks of consecutive configurations through their copies in the return part. Hence $\varphi_M$ is satisfiable iff $M$ halts.

## Sources

- L. Bozzelli, A. Murano and A. Peron, "Timed Context-Free Temporal Logics", in *Proceedings of the Ninth International Symposium on Games, Automata, Logics, and Formal Verification (GandALF 2018)*, Electronic Proceedings in Theoretical Computer Science 277, 2018, pp. 235–249, <https://doi.org/10.4204/EPTCS.277.17>; numbers from arXiv:1911.08406v1, <https://arxiv.org/abs/1911.08406v1>: Theorem 6 and its proof, Theorem 5, and the discussion of known results in Sections 1 and 4.
- J. Ouaknine and J. Worrell, "On Metric Temporal Logic and Faulty Turing Machines", in *Foundations of Software Science and Computation Structures (FoSSaCS 2006)*, Lecture Notes in Computer Science 3921, Springer, 2006, pp. 217–230, <https://doi.org/10.1007/11690634_15>: undecidability of future MTL over infinite timed words, as recalled in Section 4 of the version of the first source read.
- J. Ouaknine and J. Worrell, "On the decidability and complexity of metric temporal logic over finite words", *Logical Methods in Computer Science* 3(1), 2007, paper 8, <https://doi.org/10.2168/LMCS-3(1:8)2007>: decidability of future MTL over finite timed words, as recalled in Section 4 of the version of the first source read.
