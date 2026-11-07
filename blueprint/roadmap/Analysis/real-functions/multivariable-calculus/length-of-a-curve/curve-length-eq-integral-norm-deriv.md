# Length of a $C^1$ curve

Let $E$ be a real Banach space, let $a \le b$ be real numbers,
and let $\gamma : \mathbb{R} \to E$ be continuously differentiable on $[a, b]$. Then the total
variation of $\gamma$ on $[a, b]$ (its length, a priori a value in $[0, \infty]$) equals
$\int_a^b \lVert \gamma'(t) \rVert \, dt$.

Proof: Extend the derivative of $\gamma$ relative to $[a, b]$ by zero outside the interval and
identify the vector measure of its primitive with the corresponding density vector measure. The
variation of that measure is the integral of the norm, and the ordinary derivative agrees with the
derivative relative to $[a, b]$ almost everywhere on the interval.

## Sources

- W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 6; stable ref https://en.wikipedia.org/wiki/Arc_length.
