# For weights summing to 1, the mean vector of $AX + b$ is $A\bar X + b$

Let $\Omega$ be a finite set and $p : \Omega \to \mathbb{R}$ weights with
$\sum_{\omega \in \Omega} p(\omega) = 1$; they need not be nonnegative. For every map
$X : \Omega \to \mathbb{R}^n$, every real $m \times n$ matrix $A$ and every $b \in \mathbb{R}^m$,
the [weighted mean vector](mean-vec.md) of $\omega \mapsto A X(\omega) + b$ is

$$\overline{AX + b} = A\,\bar X + b,$$

where $\bar X_i = \sum_\omega p(\omega) X_i(\omega)$. The linear part,
$\overline{AX} = A \bar X$, holds for every weight; the total weight is used for the constant: for
weights with total $s$, the weighted mean of the constant vector $b$ is $s\,b$. For a probability
distribution on $\Omega$ (also $p \ge 0$), this is the exact affine law for the mean of a random
vector.
