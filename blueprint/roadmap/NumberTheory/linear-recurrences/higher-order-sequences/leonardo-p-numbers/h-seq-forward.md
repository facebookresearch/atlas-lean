# Forward evaluation of the $H(p)$ recurrence

For a natural number $p$, a function
$s : \mathbb{Z} \to \mathbb{Z}$ and $n \in \mathbb{N}$, this is the list of the $2p + n + 1$
values at $-p, -p+1, \dots, p+n$ (the entry at position $i$ is the value at $i - p$) of the
sequence $H$ that equals $s$ on $[-p, p]$ and continues by the $H(p)$ recurrence
$H(t) = H(t-1) + H(t-p) - H(t-2p-1)$ for $t > p$. Each step appends one value to the previous
list, so evaluation takes polynomial time.

For $p = 0$, where this rule is circular, every appended value is $0$.
