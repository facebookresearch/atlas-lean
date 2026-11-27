# Rademacher complexity of l1-bounded linear predictors

Let $\phi : Z \to \mathbb{R}^n$ be a feature map, $B \ge 0$, and let $F = \{z \mapsto \langle w, \phi(z)\rangle : \sum_{j} |w_j| \le B\}$. If a sample $S = (z_1, \dots, z_m)$, $m \ge 1$, satisfies $|\phi(z_i)_j| \le R$ for all $i$ and $j$, then

$$
\hat{R}_S(F) \le B R \sqrt{\frac{2\ln(2n)}{m}}.
$$

Compared with the Euclidean-ball bound $BR/\sqrt{m}$, the constraint on $w$ is stronger and the assumption on the features weaker, at the price of a factor $\sqrt{2\ln(2n)}$.

## Proof sketch

For a fixed sign vector, Hölder's inequality bounds the correlation of $w$ with the signs by $B\max_j |c_j|$, where $c_j$ is the correlation of the $j$-th feature coordinate with the signs; this maximum is attained at one of the $2n$ vertices $\pm B e_j$ of the $\ell_1$ ball. Massart's lemma for these $2n$ vectors, whose entries are bounded by $BR$, gives the bound.

## Depends on

- [Empirical Rademacher complexity](../rademacher-complexity/rademacher-complexity.md)
- [Massart's finite-class lemma](../rademacher-complexity/rademacher-complexity-le-of-finite.md)
- [Rademacher average of a ball of linear predictors](../rademacher-average-linear-ball-le.md)

## Proof depends on

- [Massart's finite-class lemma](../rademacher-complexity/rademacher-complexity-le-of-finite.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
