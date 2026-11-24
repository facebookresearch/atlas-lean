# The reduction for one key and one coin

For an eavesdropper $A$, a public key $y$ and coins $r$, write $Q_b$ for the probability that the
[reduction](reduction.md) outputs $1$ in world $b$ of the
[residuosity experiment](qr-exp.md), and $E_b$ for the probability that $A$ outputs $1$ on an
encryption of its message $m_b$ (both over the uniform unit $x$ only). Then
$Q_1 + E_0 = Q_0 + E_1$. When $m_0 = m_1$ both $Q_b$ vanish and $E_0 = E_1$; otherwise $Q_0 = E_0$ and
$Q_1 = E_1$.
