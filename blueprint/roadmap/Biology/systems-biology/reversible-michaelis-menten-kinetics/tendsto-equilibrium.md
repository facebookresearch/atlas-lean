# Positive rates and totals: nonnegative solutions tend to equilibrium

Let $k_1, k_{-1}, k_2, k_{-2} > 0$ and let $(s, c, e, p)$ be a [solution](is-solution.md) of the
reversible Michaelis–Menten system with $s(0), c(0), e(0), p(0) \ge 0$, total enzyme
$E_T = e(0) + c(0) > 0$ and total substrate $S_T = s(0) + c(0) + p(0) > 0$. Then there is a zero
$x_* = (s_*, c_*, e_*, p_*)$ of the [reversible field](rev-field.md) with positive coordinates,
$e_* + c_* = E_T$ and $s_* + c_* + p_* = S_T$, such that $(s(t), c(t), e(t), p(t)) \to x_*$ as
$t \to \infty$. It is the only nonnegative equilibrium of the compatibility class, by
[existence and uniqueness of the equilibrium](exists-unique-equilibrium.md). The proof applies
LaSalle's invariance principle with the
[pseudo-Helmholtz function](../complex-balancing-and-the-deficiency-zero-theore/pseudo-helmholtz.md)
relative to $x_*$.
