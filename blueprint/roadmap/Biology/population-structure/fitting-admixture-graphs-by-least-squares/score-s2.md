# The qpGraph score S2

Let $\iota$ be a finite index set. For a real $\iota \times \iota$ matrix $Q$, a real number $\lambda$ and vectors $f, g \in \mathbb{R}^\iota$, the score is

$$S_2(g) = -\sum_{i \in \iota} \frac{(g_i - f_i)^2}{Q_{ii} + \lambda},$$

with the convention $x/0 = 0$ for a term with $Q_{ii} + \lambda = 0$ (Patterson et al. 2012, eq. 7).

When every $Q_{ii} + \lambda$ is positive, maximizing $S_2$ is weighted least squares. Patterson et al. (2012, eq. 7) include a factor $\frac{1}{2}$, so their score is half of $S_2$; with the scaling here, $S_2 = 2 S_1$ for diagonal $Q$ and $\lambda = 0$ ([diagonal case](score-s2-eq-score-s1-diagonal.md)).

## Sources

- N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck, T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093, eqs. (6)–(7).
