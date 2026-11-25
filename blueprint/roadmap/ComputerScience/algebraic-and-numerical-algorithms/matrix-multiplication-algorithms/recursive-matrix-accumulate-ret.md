# Correctness of the recursive matrix multiply-accumulate

Let $\alpha$ be an additive
commutative monoid with a multiplication, let $k$ be a natural number and $n = 2^k$, and let
$A = (a_{ij})$, $B = (b_{ij})$, $C$ be $n \times n$ matrices over $\alpha$, with indices running
from $0$ to $n - 1$. Viewed as a matrix, the result returned by the recursive multiply-accumulate
procedure on $A$, $B$, $C$ equals $C + AB$, where $AB$ is the matrix product with entries
$(AB)_{ij} = \sum_{t < n} a_{it} b_{tj}$.
