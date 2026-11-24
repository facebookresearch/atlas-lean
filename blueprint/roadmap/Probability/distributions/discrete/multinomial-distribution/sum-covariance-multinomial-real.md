# Covariance of the multinomial distribution

Let $\iota$ be a finite set, $N \in \mathbb{N}$ and $p$ a probability vector on $\iota$ ($p_l \ge 0$,
$\sum_l p_l = 1$). For all $i, j \in \iota$,

$$\sum_{x} (x_i - N p_i)(x_j - N p_j)\, M_N(p; x) = N \bigl( [i = j]\, p_i - p_i p_j \bigr),$$

the sum running over the count vectors $x$ with total $N$ and $M_N$ being the [multinomial mass
function](multinomial-real.md). In particular $\operatorname{Var} X_i = N p_i (1 - p_i)$ and
$\operatorname{Cov}(X_i, X_j) = -N p_i p_j$ for $i \ne j$.

## Sources

- W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed., Wiley, 1968, Section VI.9.
