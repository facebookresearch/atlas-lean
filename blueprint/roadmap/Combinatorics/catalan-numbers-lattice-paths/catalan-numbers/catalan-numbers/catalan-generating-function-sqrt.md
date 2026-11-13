# Closed form of the Catalan generating function

Let $C_n$ be the $n$th Catalan number.
For every real number $x$ with $|x| < 1/4$ and $x \neq 0$,

$$
\sum_{n=0}^{\infty} C_n x^n = \frac{1 - \sqrt{1 - 4x}}{2x}.
$$

The hypothesis $x \neq 0$ excludes the removable singularity of the right-hand side at $x = 0$.

## Sources

- Paul Barry, "A Note on a Family of Generalized Pascal Matrices Defined by Riordan Arrays", Journal of Integer Sequences 16 (2013), Article 13.5.4, proposition lines 380–388, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.tex>. Mathlib has `PowerSeries.catalanSeries` and its quadratic functional equation, but its source file explicitly lists the square-root closed form as a TODO; this theorem records the analytic closed form rather than duplicating the formal series definition.
