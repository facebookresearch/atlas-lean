# Landen formula for generalized poly-Bernoulli numbers $C_n$

Let
$g = (g_0, g_1, \dots, g_s)$ be Landen data whose matrices $g_1, \dots, g_s$ are invertible, where
$(c_0, d_0)$ is the bottom row of $g_0$. Let $\tilde g$ be the transformed data: $\tilde g_0$ has
rows $(1, -1)$ and $(-d_0, -c_0)$, and $\tilde g_i = h g_i$ for $1 \le i \le s$, where $h$ is the
matrix with rows $(1, 0)$ and $(c_0 - d_0, -1)$. Let $\beta, \gamma \in \mathbb{R}^s$, let $k$ be a
composition of a natural number $m$ (the empty index when $m = 0$), and write $k\uparrow$ for $k$
with its last entry increased by $1$ ($k\uparrow$ is empty when $k$ is). Let
$z(t) \in \mathbb{R}[[t]]$, the variable of $g$, be the power series of
$(e^t - 1)/(c_0 e^t + d_0)$ (the zero series when $c_0 + d_0 = 0$). Then for every $n \ge 0$,

$$C_n^{(k, g, (\beta, \gamma))} =
(-1)^{n+1} \, n! \, [t^n] \, \frac{d}{dt}
\mathrm{Li}_{k\uparrow}(\tilde g; (\beta, \gamma); z(t)),$$

where $C_n$ is the generalized poly-Bernoulli number of the first kind, $\mathrm{Li}$ is Kamano's
generalized multiple polylogarithm and $[t^n] F$ is the coefficient of $t^n$ in $F$. Here
$\tilde g$ is evaluated at the variable $z(t)$ of $g$, not at its own variable.

This is Theorem 5 in the reading its proof establishes: the proof differentiates
$\mathrm{Li}_{k\uparrow}(g; z(t)) = \mathrm{Li}_{k\uparrow}(\tilde g; z(-t))$. The paper's sign
$(-1)^{n-1}$ equals $(-1)^{n+1}$ for all $n \ge 0$.

As printed, with $C_n^{(k, \tilde g, (\beta, \gamma))}$ formed from the variable
$(e^t - 1)/(-d_0 e^t - c_0) = z(-t)$ of $\tilde g$, the theorem is false: then
$C_n^{(k, \tilde g, (\beta, \gamma))} = C_n^{(k, g, (\beta, \gamma))}$ for all $n$. For instance,
$s = 1$, $g_0$ with rows $(1, -1)$ and $(1, 0)$, $g_1$ the identity matrix, $\beta = \gamma = (1)$,
$k = (1)$ and $n = 0$ give
$C_0^{(k, g, (\beta, \gamma))} = C_0^{(k, \tilde g, (\beta, \gamma))} = 1$, while the printed
identity asks for $1 = -1$.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 5.
