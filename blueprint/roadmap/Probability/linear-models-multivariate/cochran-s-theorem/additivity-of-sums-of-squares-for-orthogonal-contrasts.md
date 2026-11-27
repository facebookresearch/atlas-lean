# Additivity of sums of squares for orthogonal contrasts

In a balanced one-way layout with $g$ groups of $m \ge 1$ observations, let $c_1, \dots, c_q$ ($1 \le q \le g - 1$) be nonzero contrast vectors in $\mathbb{R}^g$ (each summing to zero) that are mutually orthogonal, and let $SS(c) = m(\sum_j c_j \bar y_j)^2/\sum_j c_j^2$. Then $\sum_k SS(c_k)$ is the squared length of the projection of the vector of group means, scaled by $\sqrt m$, onto the span of $c_1, \dots, c_q$, so it is at most the between-group sum of squares $m\sum_j(\bar y_j - \bar y)^2$; it equals it for every response vector exactly when $q = g - 1$, so that the contrasts span the space of contrasts. With unequal group sizes $n_j \ge 1$ the same holds with $SS(c) = (\sum_j c_j\bar y_j)^2/\sum_j (c_j^2/n_j)$, orthogonality $\sum_j c_jd_j/n_j = 0$, and between-group sum of squares $\sum_j n_j(\bar y_j - \bar y)^2$ with $\bar y$ the size-weighted grand mean.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Squared norm of an orthogonal projection onto the span of an orthogonal family equals the sum of the squared norms of the projections onto each vector.

## Sources

- D. Nettleton, *Statistics 510*, notes 9 "Orthogonal linear combinations, contrasts, and additional partitioning of ANOVA sums of squares", Iowa State University, 2019, <https://dnett.github.io/S510/09OrthogonalContrasts.pdf>, slides 2–6
