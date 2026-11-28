# The multi-dimensional long-run average problem for natural-valued VASS is undecidable

For vector addition systems with states whose counters must stay nonnegative, it is undecidable whether some infinite computation keeps the long-run average of every counter, taken over its selected states, below a given threshold vector; for integer-valued counters the problem is NP-complete.

**Setting (Chatterjee, Henzinger and Otop).** A $k$-dimensional *vector addition system with states* $\mathcal A = \langle Q, Q_0, \delta \rangle$ has states $Q$, initial states $Q_0$ and transitions $\delta \subseteq Q \times Q \times \mathbb Z^k$; a computation is an infinite sequence of configurations $(q, \vec x)$ starting in $Q_0 \times \{\vec 0\}$, each step adding the vector of a transition. In a *natural-valued* VASS, $\mathrm{VASS}(\mathbb N)$, all counter values along a computation must be nonnegative; in an integer-valued one, $\mathrm{VASS}(\mathbb Z)$, they range over $\mathbb Z$. For a set $S \subseteq Q$ of *selecting states* and a counter $i$, the limit-average of counter $i$ over $S$ along a computation $\pi$ is $\liminf_{n} \frac1m \sum_{j=1}^{m} \vec x_j[i]$, where $(s_1, \vec x_1), \dots, (s_m, \vec x_m)$ are the configurations of the prefix of length $n$ whose state is in $S$; it is defined when $\pi$ visits $S$ infinitely often. The *multi-dimensional average problem* asks, given a VASS, a tuple $\vec S = (S[1], \dots, S[k])$ of sets of selecting states and a threshold vector $\vec\lambda \in \mathbb Q^k$, whether some computation has all $k$ limit-averages defined and componentwise at most $\vec\lambda$.

**Theorem (Chatterjee, Henzinger and Otop).** The multi-dimensional average problem for natural-valued VASS is undecidable.

The same paper shows that the problem is NP-complete for integer-valued VASS and for one-dimensional natural-valued VASS, and that its expected-value variant for probabilistic integer-valued VASS, and for probabilistic natural-valued VASS under the strict semantics, is solvable in polynomial time.

## Depends on

- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Long-run average cost of natural-valued VASS is undecidable](long-run-average-cost-of-natural-valued-vass-undecidable.md)

## Expansion

The reduction is from the average-value problem with state-dependent cost vectors, which is undecidable for natural-valued VASS already with threshold $0$. The source cites this threshold-$0$ case as Theorem 24 of the CONCUR 2019 paper (Theorem 26 of its arXiv version), whose page states it. As the source observes, threshold $0$ means that counter $i$ must be $0$ whenever the cost vector $\vec c_q$ of the current state is nonzero at component $i$, and the multi-dimensional average problem expresses this constraint, with $S[i]$ the set of states $q$ with $\vec c_q[i] \ne 0$ and threshold $\vec 0$.

## Sources

- Krishnendu Chatterjee, Thomas A. Henzinger and Jan Otop, "Multi-Dimensional Long-Run Average Problems for Vector Addition Systems with States", in *31st International Conference on Concurrency Theory (CONCUR 2020)*, Leibniz International Proceedings in Informatics 171, Schloss Dagstuhl, 2020, pp. 23:1–23:22, doi:[10.4230/LIPIcs.CONCUR.2020.23](https://doi.org/10.4230/LIPIcs.CONCUR.2020.23); read in arXiv:2007.08917v1 ([arXiv](https://arxiv.org/abs/2007.08917v1)), whose numbering is used: Section 2 (VASS and computations), Section 3 (averages over selecting states and the multi-dimensional average problem), Theorem 8 (Subsection 4.1, NP-completeness for integer-valued VASS), Theorem 15 (Subsection 5.1, the one-dimensional case), and Theorem 16 with the reduction in Subsection 5.2.
