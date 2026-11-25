# The Hodgkin–Huxley vector field

For a [parameter set](params.md), the Hodgkin–Huxley vector field sends a state
$x = (V, m, h, n) \in \mathbb{R}^4$ to the vector with components

$$\frac{I - I_{ion}(V, m, h, n)}{C}, \quad
\alpha_m(V)(1 - m) - \beta_m(V)\,m, \quad
\alpha_h(V)(1 - h) - \beta_h(V)\,h, \quad
\alpha_n(V)(1 - n) - \beta_n(V)\,n,$$

where $I_{ion}$ is the [total ionic current](ionic.md) and the rates are [$\alpha_m$](alpha-m.md),
[$\beta_m$](beta-m.md), [$\alpha_h$](alpha-h.md), [$\beta_h$](beta-h.md), [$\alpha_n$](alpha-n.md)
and [$\beta_n$](beta-n.md); time is in ms. With the convention $x/0 = 0$, the voltage component is
$0$ when $C = 0$; [valid parameters](valid.md) have $C > 0$.
