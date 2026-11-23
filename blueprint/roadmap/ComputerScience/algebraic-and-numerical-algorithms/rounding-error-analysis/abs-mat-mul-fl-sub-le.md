# Forward error of floating-point matrix multiplication

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. Let $p \ge 1$, let $m, n, r$ be natural numbers with $n u < 1$, and let $A$ be an $m \times n$ and $B$ an $n \times r$ matrix over $K$. Let $\hat C = \mathrm{fl}(AB)$ be the classical floating-point product, each entry $\hat C_{ij}$ being the [floating-point dot product](dot-fl.md) of row $i$ of $A$ and column $j$ of $B$, accumulated from $k = 0$ to $n - 1$. Then for all $i < m$ and $j < r$

$$|\hat C_{ij} - (AB)_{ij}| \le \gamma_n \sum_{k<n} |A_{ik}|\,|B_{kj}|,$$

that is, $|\hat C - AB| \le \gamma_n\, |A|\,|B|$ entrywise.

To first order in $u$ this is the bound $\mathrm{fl}(AB) = AB + E$ with $|E| \le n u\,|A|\,|B|$. The same error analysis also gives a componentwise backward error (each computed entry is an exact dot product of slightly perturbed rows and columns) and gives $\gamma_n$ for any order of accumulation, which covers blocked and communication-avoiding schedules; the statement above is for left-to-right accumulation.

## Informally uses

- [Forward error of the floating-point dot product](abs-dot-fl-sub-le.md): applied to row $i$ of $A$ and column $j$ of $B$.

## Sources

- J. W. Demmel, Math 221 course, UC Berkeley, Lecture 5 notes, 2024: the bound $C = \mathrm{fl}(AB) = AB + E$, $|E| \le n\,\varepsilon\,|A|\,|B|$, to first order in the machine precision $\varepsilon = u$.
- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002: the exact $\gamma_n$ form.
