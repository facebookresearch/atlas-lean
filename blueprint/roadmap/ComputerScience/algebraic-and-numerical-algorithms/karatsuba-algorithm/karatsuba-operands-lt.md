# Size bound for Karatsuba's recursive operands

Let $B \ge 1$ and $n$ be natural numbers,
let $m = \lceil n/2 \rceil$, and let $x < B^n$ be a natural number. Then the high part
$\lfloor x / B^m \rfloor$, the low part $x \bmod B^m$, and their distance
$|\lfloor x / B^m \rfloor - x \bmod B^m|$ are all less than $B^m$.

Applied to both inputs $x, y < B^n$, this bounds by $B^m$ the six operands of the three recursive
calls of Karatsuba multiplication.
