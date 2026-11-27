# Variance of a count of events with a dependency graph

Let $A_i$ be measurable events indexed by a finite set and let $G$ be a graph on the indices such that $\Pr[A_i \cap A_j] = \Pr[A_i] \Pr[A_j]$ whenever $i \neq j$ are not adjacent. Then the [count](count.md) $X = \sum_i 1_{A_i}$ satisfies

$$\operatorname{Var} X \le \mu + \Delta,$$

where $\mu = \sum_i \Pr[A_i] = \mathbb E X$ and $\Delta$ is the [correlation sum](dependent-pair-sum.md) over ordered adjacent pairs. Expanding $\operatorname{Var} X = \sum_{i,j} \operatorname{Cov}(1_{A_i}, 1_{A_j})$, the diagonal contributes at most $\mu$, adjacent pairs at most $\Pr[A_i \cap A_j]$ each, and non-adjacent pairs nothing. Only pairwise independence of non-adjacent events is needed, which is weaker than the mutual independence required by the [Lovász local lemma](../lovasz-local-lemma-symmetric-finite.md).

## Sources

- Yufei Zhao (lecturer) and Andrew Lin (notes), *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Section 4.2, the computation $\operatorname{var}(X) \le \mathbb E[X] + \Delta$ before Corollary 4.13 (there $\Delta$ is over unordered pairs; see [the correlation sum](dependent-pair-sum.md)).
