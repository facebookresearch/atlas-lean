# Diploid Baum–Eagon mean-fitness inequality, sharp form

Let $\iota$ be a finite set of alleles, $p \in \mathbb{R}^\iota$ with $p_i \ge 0$, and $w_{ij} \ge 0$ genotype fitnesses with $\bar w(p) = \sum_{i,j} p_i p_j w_{ij} > 0$. Let $p'_i = p_i m_i / \bar w(p)$, where $m_i = \sum_j \frac{w_{ij} + w_{ji}}{2} p_j$. Then

$$2 \sum_i p'_i \log\frac{p'_i}{p_i} \le \log \bar w(p') - \log \bar w(p),$$

with the conventions that division by $0$ gives $0$ and $\log 0 = 0$; since $p_i = 0$ implies $p'_i = 0$, the summands with $p_i = 0$ vanish. One generation of selection raises the log mean fitness by at least twice the relative entropy of the new allele frequencies from the old ones. The frequencies need not sum to $1$; on the simplex the left side is nonnegative by Gibbs' inequality. This is a mean-fitness monotonicity inequality obtained by Baum and Eagon's argument for the quadratic form $\bar w$, not Fisher's fundamental theorem.

## Sources

- L. E. Baum and J. A. Eagon, *An inequality with applications to statistical estimation for probabilistic functions of Markov processes and to a model for ecology*, Bull. Amer. Math. Soc. 73 (1967), 360–363.
