# Backward evaluation of the $H(p)$ recurrence

For a natural number $p$, a function
$s : \mathbb{Z} \to \mathbb{Z}$ and $n \in \mathbb{N}$, this is the list of the values at
$-p-n, \dots, p$ of the sequence $H$ that equals $s$ on $[-p, p]$ and continues to the left by
$H(t) = H(t+2p) + H(t+p+1) - H(t+2p+1)$ for $t < -p$, which is the $H(p)$ recurrence
$H(u) = H(u-1) + H(u-p) - H(u-2p-1)$ at $u = t+2p+1$ solved for $H(t)$. Each step prepends one
value to the previous list.

For $p = 0$, where this rule is circular, every prepended value equals $s(0)$.
