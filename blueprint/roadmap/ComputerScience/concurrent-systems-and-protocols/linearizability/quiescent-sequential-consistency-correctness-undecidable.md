# Correctness for quiescent sequential consistency is undecidable

Quiescent sequential consistency judges a concurrent object only at quiescent points, where no operation is pending, while keeping each process's own events in order. Deciding whether every behavior of a finite-state implementation is allowed by a finite-state specification under this condition is undecidable, in contrast to plain quiescent consistency.

**Setting (Dongol and Hierons).** Events are invocations and responses of operations, each belonging to one of finitely many processes. Implementations $\mathcal{Q}$ and specifications $\mathcal{S}$ are finite automata over these events. An invocation in a trace is *pending* if no later event is its matching response; a trace is *quiescent* if it has no pending invocation, and *end-to-end quiescent* if it is quiescent and no nonempty proper prefix of it is quiescent. A quiescent trace $\sigma = \sigma_1 \sigma_2 \cdots \sigma_m$ with every $\sigma_i$ end-to-end quiescent is *allowed by $\mathcal{S}$ under quiescent sequential consistency (QSC)* if there are permutations $\sigma'_i$ of the $\sigma_i$ that preserve, for every process, the order of that process's events, such that $\sigma'_1 \sigma'_2 \cdots \sigma'_m$ is a trace of $\mathcal{S}$. The *correctness problem* asks whether every behavior of the implementation is allowed by the specification, formally, whether the language of $\mathcal{Q}$ with quiescent points marked is contained in the closure of the language of $\mathcal{S}$ under the rewrites that QSC permits.

**Theorem (Dongol and Hierons).** The correctness problem for quiescent sequential consistency is undecidable.

For quiescent consistency without the per-process order constraint, the same paper shows correctness decidable, coNP-hard and in EXPSPACE, and in PSPACE when the number of events between quiescent points is bounded; the membership problem for a single trace is NP-complete.

## Depends on

- [Sequential consistency of concurrent histories](../shared-memory-objects/shared-memory-synchronization/sequential-consistency-of-concurrent-histories.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Under QSC events of different processes commute while events of one process do not, so correctness is containment in a rational trace language whose independence relation is not transitive, a situation in which containment is undecidable in general. The proof makes this concrete: from an instance $\alpha_1, \dots, \alpha_n$, $\beta_1, \dots, \beta_n$ of the Post correspondence problem, the implementation lets process $1$ produce the letters of the words $\alpha_{i_1} \cdots \alpha_{i_k}$ and process $2$ those of $\beta_{i_1} \cdots \beta_{i_k}$ as invocation and response pairs, followed by a final event, while the specification accepts exactly the traces in which the two process projections differ. Every implementation trace is then allowed exactly when the instance has no solution.

## Sources

- Brijesh Dongol and Robert M. Hierons, "Decidability and complexity for quiescent consistency and its variations", Information and Computation 257, pp. 1–21, 2017, <https://doi.org/10.1016/j.ic.2017.09.012>; the definitions of quiescent and end-to-end quiescent traces and of the membership and correctness problems in Section 3, "Quiescent consistency", Theorem 1 (membership) in Section 4 and Theorems 3 to 6 (correctness for quiescent consistency) in Section 5, Definitions 7 and 8 (quiescent sequential consistency), and Theorem 10 in Section 8.1 of Section 8, "Correctness for quiescent sequential consistency" of arXiv:1511.08447v1, read at <https://arxiv.org/abs/1511.08447v1>.
