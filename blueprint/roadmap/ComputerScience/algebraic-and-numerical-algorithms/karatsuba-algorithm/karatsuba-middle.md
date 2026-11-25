# Karatsuba's middle coefficient

For all natural numbers $a, b, c, d$, write
$P = |a - b| \cdot |c - d|$. If $b \le a$ holds exactly when $d \le c$, then
$ac + bd - P = ad + bc$, where the subtraction is truncated at $0$; otherwise
$ac + bd + P = ad + bc$.

So the cross term $ad + bc$ is recovered from the three products $ac$, $bd$ and $P$.
