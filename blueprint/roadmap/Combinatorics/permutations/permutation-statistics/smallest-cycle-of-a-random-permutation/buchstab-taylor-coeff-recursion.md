# Recursion for the Taylor coefficients of the Buchstab function

Let $\omega$ be a real
function with $\omega(x) = 1/x$ for $1 \le x \le 2$ and
$x\,\omega(x) = 1 + \int_1^{x-1} \omega(t)\,dt$ for $x \ge 2$, and let $c_{n,i}$ ($n, i \ge 0$)
be real numbers such that for every integer $n \ge 1$ and every real $z$ with $-1 \le z < 1$ the
series $\sum_{i \ge 0} c_{n,i} z^i$ converges absolutely to $\omega(n + (1+z)/2)$. Then
$c_{1,i} = \frac{2}{3} \left(-\frac{1}{3}\right)^i$ for every $i \ge 0$, and for every $n \ge 1$

$$c_{n+1,0} = \frac{1}{2n+3} \sum_{i \ge 0} c_{n,i} \left(2(n+1) + \frac{(-1)^i}{i+1}\right)$$

and, for every $i \ge 1$,

$$c_{n+1,i} = \frac{1}{2n+3} \left(\frac{c_{n,i-1}}{i} - c_{n+1,i-1}\right).$$

The printed statement of Theorem 3 has $c_{n,i}/n$ in place of $c_{n,i-1}/i$; the recursion above
is the identity $(2n+3) c_{n+1,i} + c_{n+1,i-1} = c_{n,i-1}/i$ derived in the paper's proof.

## Sources

- Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab Function and Revisiting the Variance of the Distribution of the Smallest Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 3.
