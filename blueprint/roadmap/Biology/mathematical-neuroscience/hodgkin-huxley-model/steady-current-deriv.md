# Derivative of the steady-state current

For a [parameter set](params.md) and a voltage $V$, write $m$, $h$ and $n$ for the steady states
$m_\infty(V)$, $h_\infty(V)$ and $n_\infty(V)$ ([$m_\infty$](m-inf.md), [$h_\infty$](h-inf.md),
[$n_\infty$](n-inf.md)), and put $m' = m\,(1 - m)\,\lambda_m(V)$, $h' = h\,(1 - h)\,\lambda_h(V)$
and $n' = n\,(1 - n)\,\lambda_n(V)$, with the logarithmic derivatives [$\lambda_m$](lam-m.md),
[$\lambda_h$](lam-h.md) and [$\lambda_n$](lam-n.md). The derivative of the steady-state current is

$$I_\infty'(V) = g_{Na}\,\bigl(3 m^2 m' h + m^3 h'\bigr)(V - E_{Na}) + g_{Na}\, m^3 h +
4 g_K\, n^3 n'\,(V - E_K) + g_K\, n^4 + g_L.$$

For every parameter set it is the derivative at $V$ of the
[steady-state current](steady-current.md), since $m'$, $h'$ and $n'$ are the derivatives of the
steady states at $V$.
