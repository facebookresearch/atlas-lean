# Deterministic half of the Wiener isometry

Let $t \ge 0$, $a, b \in \mathbb{R}^2$, and let
$y_a, y_b, \kappa_a, \kappa_b : \mathbb{R} \to \mathbb{R}^2$ and $K, G$ (stored symmetric matrices)
be continuous on $[0, t]$, with $y_a' = -\kappa_a$ and $y_b' = -\kappa_b$ on $(0, t)$, $y_a(t) = a$,
$y_b(t) = b$, $K(0) = 0$ and $K' = G$ on $(0, t)$. Then, with $\langle u, C v \rangle$ the
[bilinear form](quad-form.md),

$$
\begin{aligned}
&\langle b, K(t)\, a \rangle + \int_0^t \langle b, K(\min(t, s))\, \kappa_a(s) \rangle\, ds \\
&\quad + \int_0^t \Bigl(\langle \kappa_b(s), K(\min(s, t))\, a \rangle +
\int_0^t \langle \kappa_b(s), K(\min(s, r))\, \kappa_a(r) \rangle\, dr\Bigr) ds \\
&= \int_0^t \langle y_b(s), G(s)\, y_a(s) \rangle\, ds.
\end{aligned}
$$

With $K$ the covariance of the driving martingale, the left side is the second moment of two Wiener
integrals in integration-by-parts form.
