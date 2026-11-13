# Successor step of the truncated M-rule length

Let $k, f \in \mathbb{N}$ and
$x \in \mathbb{N}^{k+1}$, and write $M_f(x)$ for the number of M-rule steps from $x$ in
Slow$\{k\}$-Nim on $k + 1$ stacks, counted for at most $f$ steps. Then $M_{f+1}(x) = 0$ if $x$
has no options, and otherwise $M_{f+1}(x) = 1 + M_f(x')$, where $x'$ is the position obtained
from $x$ by the M-move.

## Sources

- Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1, Section 1.2 (the function `M`).
