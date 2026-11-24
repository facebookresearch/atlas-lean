# Correctness of the satisfy-count

Let $m$ be a natural number and $t$ a diagram ordered
from $0$ (tested variables strictly increase along every path) in which every tested variable is
below $m$. Then for every assignment $\sigma$, the satisfy-count of $t$ below $m$ equals the model
count of the function $\tau \mapsto t(\tau)$ over the variables $0, 1, \dots, m - 1$ from
$\sigma$, where $t(\tau)$ is the value of $t$ under $\tau$. In other words, it is the number of
assignments to the variables $0, \dots, m - 1$ that make $t$ true.
