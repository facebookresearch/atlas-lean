# Equilibria of the Hodgkin–Huxley equations for valid parameters

Let the parameters be [valid](valid.md). A state $x = (V, m, h, n)$ is a zero of the
[Hodgkin–Huxley vector field](field.md) exactly when $m = m_\infty(V)$, $h = h_\infty(V)$,
$n = n_\infty(V)$ and

$$I_{ion}(V, m_\infty(V), h_\infty(V), n_\infty(V)) = I,$$

where $m_\infty = \alpha_m/(\alpha_m + \beta_m)$, $h_\infty$ and $n_\infty$ are the
[steady states](steady.md) of the gating kinetics and $I_{ion}$ is the
[total ionic current](ionic.md). So the equilibria are the states
$(V, m_\infty(V), h_\infty(V), n_\infty(V))$ at which the [steady-state current](steady-current.md)
equals the applied current $I$.
