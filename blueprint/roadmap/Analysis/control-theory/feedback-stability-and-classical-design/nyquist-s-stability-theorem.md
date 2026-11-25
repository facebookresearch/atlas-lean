# Nyquist's stability theorem

Let $L = n/d$ be a proper rational loop transfer function with real coefficients and coprime $n, d$, in negative unity feedback, so that the closed-loop poles are the roots of $d + n$, the zeros of $1 + L$. Let $R > 0$ be larger than the modulus of every root of $d$ and of $d + n$, and let $\Gamma$ be the Nyquist contour traversed clockwise: the imaginary axis from $-iR$ to $iR$, indented to the right by small semicircles around the imaginary-axis poles of $L$, closed by the right half-circle of radius $R$. Assume $1 + L$ has no zeros on $\Gamma$. Let $P$ be the number of poles of $L$, and $Z$ the number of zeros of $1 + L$, inside $\Gamma$, counted with multiplicity, and let $N$ be the net number of clockwise encirclements of $-1$ by the closed curve $L(\Gamma)$. Then:

1. **Nyquist's theorem.** $Z = N + P$. For small enough indentations, $P$ is the number of poles of $L$ in the open right half-plane and $Z$ is the number of closed-loop poles in the open right half-plane.
2. **Simplified criterion.** If $L$ has no poles in the open right half-plane, the closed loop is stable (all roots of $d + n$ in the open left half-plane) if and only if $L(\Gamma)$ does not pass through $-1$ and $N = 0$, with the indentation hypothesis covering imaginary-axis poles of $L$.

## Expansion

The proof is the principle of variation of the argument applied to $f = 1 + L$ on the region bounded by $\Gamma$: the number of clockwise turns of $f(\Gamma)$ about $0$, which equals the number of clockwise turns of $L(\Gamma)$ about $-1$, is $Z - P$, because the poles of $f$ are those of $L$ and coprimality prevents cancellation between $d$ and $d + n$. The [argument principle on a piecewise-smooth Jordan contour](../../complex-analysis/cauchy-theory/argument-principle/argument-principle-on-a-piecewise-smooth-jordan-contour.md) gives the count, and [the large and small arcs of the Nyquist contour](the-large-and-small-arcs-of-the-nyquist-contour.md) supply the remaining facts about the contour.

## Proof depends on

- [Argument principle on a piecewise-smooth Jordan contour](../../complex-analysis/cauchy-theory/argument-principle/argument-principle-on-a-piecewise-smooth-jordan-contour.md): the counting formula $Z - P$ for $1 + L$ on the Nyquist contour
- [The large and small arcs of the Nyquist contour](the-large-and-small-arcs-of-the-nyquist-contour.md): the arcs contribute no zeros or poles, and the counts inside the contour are those of the open right half-plane

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 10.2: Theorem 10.1 (simplified Nyquist criterion, loop transfer function without poles in the right half-plane, p. 10-5), the Nyquist contour with semicircular indentations around imaginary-axis poles, Theorem 10.2 (Nyquist's stability theorem, $Z = N + P$, p. 10-10), and Theorem 10.3 (principle of variation of the argument, winding number $Z - P$, p. 10-11).
