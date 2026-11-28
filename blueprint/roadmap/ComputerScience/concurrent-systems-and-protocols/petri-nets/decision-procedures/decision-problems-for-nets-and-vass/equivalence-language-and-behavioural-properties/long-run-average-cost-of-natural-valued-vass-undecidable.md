# Long-run average cost of natural-valued VASS is undecidable

For vector addition systems with states whose counters must stay nonnegative, and cost functions that weigh the counter values linearly with coefficients depending on the state, it is undecidable whether some computation has long-run average cost at most a given threshold, even restricted to lasso-shaped computations.

**Setting (Chatterjee, Henzinger and Otop).** A $k$-dimensional *vector addition system with states* (VASS) $\mathcal{A} = \langle Q, Q_0, \delta \rangle$ has a finite set of states $Q$, initial states $Q_0 \subseteq Q$ and transitions $\delta \subseteq Q \times Q \times \mathbb{Z}^k$. A configuration is a pair $(q, \vec{x}) \in Q \times \mathbb{Z}^k$. A *computation* is an infinite sequence of configurations starting in $Q_0 \times \{\vec{0}\}$ in which each step $(q, \vec{x}) \to (q', \vec{x} + \vec{y})$ uses a transition $(q, q', \vec{y}) \in \delta$; for a *natural-valued* VASS, $\mathrm{VASS}(\mathbb{N})$, all counter values along the computation must be nonnegative. A computation is *regular* if its path is ultimately periodic, $\alpha \beta^\omega$. A *cost function* assigns to each state $q$ a vector $\vec{a}_q \in \mathbb{N}^k$ and to each configuration the value $f(q, \vec{z}) = \vec{a}_q \cdot \vec{z}$; it is *uniform* if $\vec{a}_q$ does not depend on $q$. The long-run average of a computation $\pi$ is $\liminf_{n \to \infty} \frac{1}{n+1} \sum_{i=0}^{n} f(\pi[i])$. The *average-value problem* (respectively the *regular average-value problem*) asks, given a VASS, a cost function and a threshold $\lambda \in \mathbb{Q}$, whether some computation (respectively some regular computation) has long-run average at most $\lambda$.

**Theorem (Chatterjee, Henzinger and Otop).** The average-value and the regular average-value problems for natural-valued VASS with general (not necessarily uniform) cost functions are undecidable, already for the threshold $\lambda = 0$.

In contrast, the same paper shows that for natural-valued VASS and uniform cost functions with nonzero coefficients both problems are decidable (and mutually reducible to configuration reachability), that for integer-valued VASS the regular problem is NP-complete for general cost functions, and that both problems are decidable in polynomial time for integer-valued VASS and uniform cost functions.

## Depends on

- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from the halting problem for two-counter Minsky machines. The VASS reads encodings of repeated machine computations separated by $\#$, checks in its finite control that they follow the instructions assuming the zero and nonzero tests are correct, and keeps counters $c_i$ equal to $\max(0, r_i - 1)$ for the registers $r_i$, while its state records whether $r_i$ is $0$, $1$ or $c_i + 1$. Wrong guesses cannot be prevented, since VASS transitions do not depend on counter values, so the cost function returns $c_i$ whenever the state claims that $r_i$ is $0$ or $1$. Costs are natural numbers, so a regular computation has average $0$ only if every such claim is correct, which happens exactly when the repeated words encode terminating computations of the machine.

## Sources

- Krishnendu Chatterjee, Thomas A. Henzinger and Jan Otop, "Long-Run Average Behavior of Vector Addition Systems with States", 30th International Conference on Concurrency Theory (CONCUR 2019), LIPIcs 140, Article 27, 2019, <https://doi.org/10.4230/LIPIcs.CONCUR.2019.27>; Section 2 (VASS, computations, cost functions and the average-value problems), Theorem 26 in Section 5 ("General cost functions and VASS(N)") with its proof sketch, and the summary of results in the introduction, read in arXiv:1905.05537v1, <https://arxiv.org/abs/1905.05537v1>.
