# Exponential generating function of a shifted Stirling column

Write $S(n,k)$ for the
Stirling numbers of the second kind. For every natural number $j$ and every real number $x$, the
series

$$\sum_{n=0}^{\infty} S(n+1,j+1)\, \frac{x^n}{n!}$$

converges unconditionally to $e^x (e^x - 1)^j / j!$.

## Sources

- Ronald L. Graham, Donald E. Knuth, and Oren Patashnik, *Concrete Mathematics: A Foundation for Computer Science*, 2nd ed., Addison-Wesley, 1994, Section 7.6 (the column generating function `(e^x - 1)^(j+1)/(j+1)!`, differentiated).
