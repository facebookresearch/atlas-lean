# Leak reversal potential of the squid giant axon

The leak reversal potential of the [squid parameters](squid.md), in mV:

$$E_L = \frac{36 \cdot 12\, n_\infty(0)^4 - 120 \cdot 115\, m_\infty(0)^3 h_\infty(0)}{0.3},$$

where $m_\infty(0)$, $h_\infty(0)$ and $n_\infty(0)$ are the resting gating values
([sodium activation](m-rest.md), [sodium inactivation](h-rest.md),
[potassium activation](n-rest.md)). It is the value that makes the [total ionic current](ionic.md)
vanish at the resting state:
$120\, m_\infty(0)^3 h_\infty(0)\,(0 - 115) + 36\, n_\infty(0)^4\,(0 + 12) + 0.3\,(0 - E_L) = 0$. It
lies [between $E_K = -12$ and $E_{Na} = 115$](squid-el-mem.md).
