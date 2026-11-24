# Second moment method for counts of events

Let $A_i$ be measurable events indexed by a finite set and $G$ a dependency graph for them in the pairwise sense of the [variance bound](variance-sum-indicator-le.md). If $\mu = \sum_i \Pr[A_i] > 0$, then

$$\Pr[\text{no } A_i \text{ occurs}] \le \frac{\mu + \Delta}{\mu^2},$$

with $\Delta$ the [correlation sum](dependent-pair-sum.md) over ordered adjacent pairs. Hence along a sequence with $\mu \to \infty$ and $\Delta = o(\mu^2)$ some $A_i$ occurs with high probability. Applied to the copies of a balanced graph $H$ in $G(n, p)$ this gives the upper half of the threshold $n^{-1/m(H)}$ (Zhao, Theorem 4.18); [Janson's inequality](../janson-s-inequalities/README.md) improves the polynomial bound to an exponential one.

## Informally uses

- [Second moment method](measure-real-eq-zero-le-variance-div-sq.md): applied to the count $X$.
- [Variance of a count of events with a dependency graph](variance-sum-indicator-le.md): bounds $\operatorname{Var} X$ by $\mu + \Delta$.

## Sources

- Yufei Zhao (lecturer) and Andrew Lin (notes), *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Lemma 4.8 and Corollary 4.13.
