# Kolmogorov continuity theorem

Let $(\Omega, \mu)$ be a probability space and $X = (X_t)_{t \in \mathbb{R}}$ a real process, and let
$\alpha, \beta > 0$ and $K \ge 0$ be such that for all $s, t$ the variable $|X_s - X_t|^\beta$ is integrable
and $\mathbb E |X_s - X_t|^\beta \le K |s - t|^{1 + \alpha}$. Then for every $\gamma$ with
$0 < \gamma < \alpha/\beta$ there is a modification $Y$ of $X$ ($Y_t = X_t$ almost surely for each $t$; one
may take $Y = X$) such that, almost surely, for some $C > 0$,

$$|Y_q - Y_r| \le C |q - r|^\gamma \qquad \text{for all dyadic rationals } q, r \in [0, 1] .$$

This is the probabilistic core of Kolmogorov's lemma: the conclusion only concerns dyadic times, and
the extension to a modification that is continuous (indeed $\gamma$-Hölder) at all times is the
[Kolmogorov continuous-modification theorem for real-valued
processes](exists-continuous-modification.md).

## Sources

- J.-F. Le Gall, DEA lecture notes, 1994, Lemme 2.3.
