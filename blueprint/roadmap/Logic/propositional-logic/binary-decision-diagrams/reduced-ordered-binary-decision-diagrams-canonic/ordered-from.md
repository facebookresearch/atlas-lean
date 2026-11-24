# Diagrams ordered from a variable

For a natural number $n$, a diagram is ordered from
$n$ when every variable it tests is at least $n$ and the tested variables strictly increase
along every path. Recursively: every leaf is ordered from $n$, and the node testing $v$ with
children $\ell$ and $h$ is ordered from $n$ when $n \le v$ and both $\ell$ and $h$ are ordered
from $v + 1$.
