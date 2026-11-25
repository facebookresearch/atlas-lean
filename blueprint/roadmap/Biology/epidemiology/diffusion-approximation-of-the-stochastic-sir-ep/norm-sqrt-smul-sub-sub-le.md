# Kurtz's pathwise estimate for the fluctuations

Let $\beta, \gamma \ge 0$, $N \in \mathbb{N}$, and real $B \ge 0$, $\delta \le 1$, $\rho$ and $k$,
with the sup norm $\|h\| = \max(|h_1|, |h_2|)$ on $\mathbb{R}^2$. Let $x$ be continuous on $[0, T]$
with $\|x(t)\| \le B$ and $x(t) = x(0) + \int_0^t F(x(s))\, ds$ there, for the [drift](drift.md)
$F$. Let $X : \mathbb{R} \to \mathbb{R}^2$ be measurable with $\|X(t) - x(t)\| \le \delta$ on
$[0, T]$, and let $U$ be a [fluctuation path](is-fluctuation-path.md): $U$ is continuous on $[0, T]$
and $U(t) = u_0 + (m(t) - m(0)) + \int_0^t DF(x(s))\, U(s)\, ds$ for $t \in [0, T]$, with
$\|u_0\| \le k$ and $\|m(t)\| \le k$ on $[0, T]$. If $\|\sqrt N (X(0) - x(0)) - u_0\| \le \rho$ and
$\|\sqrt N \bigl(X(t) - X(0) - \int_0^t F(X(s))\, ds\bigr) - m(t)\| \le \rho$ for $t \in [0, T]$,
then for every $t \in [0, T]$

$$
\bigl\|\sqrt N\, (X(t) - x(t)) - U(t)\bigr\| \le
\bigl(3 \rho + \beta \delta T \cdot 3 k\, e^{L T}\bigr)\, e^{(L + \beta) T},
\qquad L = 2 \beta B + \gamma.
$$

The proof writes $\sqrt N (F(X) - F(x)) = DF(x)\, U_N + \beta (U_N)_1 (X - x)_2\, (-1, 1)$ with
$U_N = \sqrt N (X - x)$, by the [exact second-order expansion](drift-add.md), and applies Gronwall's
inequality to $\|U_N - U\|$.
