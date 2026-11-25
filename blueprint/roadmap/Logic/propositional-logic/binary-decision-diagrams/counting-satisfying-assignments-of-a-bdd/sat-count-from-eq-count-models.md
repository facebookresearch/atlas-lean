# The satisfy-count from a variable counts models

Let $m$ and $n$ be natural numbers and
$t$ a diagram ordered from $n$ (every tested variable is at least $n$, and tested variables
strictly increase along every path) in which every tested variable is below $m$. Then for every
assignment $\sigma$, the one-pass satisfy-count $c_m(n, t)$ of $t$ from $n$ with bound $m$ equals
the model count of the function $\tau \mapsto t(\tau)$ over the variables $n, n + 1, \dots, m - 1$
from $\sigma$ (no variables when $m \le n$), where $t(\tau)$ is the value of $t$ under $\tau$.
