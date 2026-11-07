# Closed form of the Catalan generating function

Let $C_n$ be the $n$th Catalan number.
For every real number $x$ with $|x| < 1/4$ and $x \neq 0$,

$$
\sum_{n=0}^{\infty} C_n x^n = \frac{1 - \sqrt{1 - 4x}}{2x}.
$$

The hypothesis $x \neq 0$ excludes the removable singularity of the right-hand side at $x = 0$.

## Sources

- Paul Barry, "A Note on a Family of Generalized Pascal Matrices Defined by Riordan Arrays", Journal of Integer Sequences 16 (2013), Article 13.5.4, proposition lines 380–388, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.tex>. Complete-source SHA-256 `2d55112a4e158236133ce50b992c0a6eb75ceb48446695581e4dbe8e35879161`; normalized proposition-span SHA-256 `d350c0634eccfd92e38924751b09c94be26086fca3c50da195c8a353910dc759`. Mathlib has `PowerSeries.catalanSeries` and its quadratic functional equation, but its source file explicitly lists the square-root closed form as a TODO; this theorem records the analytic closed form rather than duplicating the formal series definition.
