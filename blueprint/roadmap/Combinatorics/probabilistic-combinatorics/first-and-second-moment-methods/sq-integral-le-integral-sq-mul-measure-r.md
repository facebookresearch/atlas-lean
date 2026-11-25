# Second moment method, Cauchy–Schwarz form

Let $X$ be a square-integrable real random variable on a probability space with $X \ge 0$ almost
surely. Then

$$
(\mathbb E X)^2 \le \mathbb E[X^2] \cdot \Pr[X > 0],
$$

that is, $\Pr[X > 0] \ge (\mathbb E X)^2 / \mathbb E[X^2]$ whenever $\mathbb E[X^2] > 0$. It
follows from Cauchy–Schwarz applied to $X = X \cdot 1_{X > 0}$, and it is the case $\theta = 0$ of
[the Paley–Zygmund inequality](../../../Probability/concentration-inequalities/paley-zygmund.md). When $\mathbb E[X^2] > 0$ it is slightly sharper than the
[Chebyshev form](measure-real-eq-zero-le-variance-div-sq.md): it gives
$\Pr[X = 0] \le \operatorname{Var} X / \mathbb E[X^2]$.
