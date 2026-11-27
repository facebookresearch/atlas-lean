# Stochastic rounding

Let $F$ be a set of floating-point numbers. For a real $x$ in the range of $F$, let $\lfloor x \rfloor$ be the largest member of $F$ at most $x$ and $\lceil x \rceil$ the smallest at least $x$. *Stochastic rounding* (in its proportional form) returns the random value

$$\mathrm{fl}(x) = \begin{cases} \lceil x \rceil & \text{with probability } p = (x - \lfloor x \rfloor)/(\lceil x \rceil - \lfloor x \rfloor), \\ \lfloor x \rfloor & \text{with probability } 1 - p, \end{cases}$$

and $\mathrm{fl}(x) = x$ when $x \in F$. In a computation each operation is rounded this way, with fresh randomness. If $F$ is the set of binary floating-point numbers of precision $t$ with unbounded exponent range, $u = 2^{-t}$, then the rounded value satisfies $\mathrm{fl}(x) = x(1 + \delta)$ with $|\delta| \le 2u$, twice the bound for round to nearest; in a format with bounded exponents the same holds for $x$ in the normal range, but not below it: for $x$ half the smallest positive subnormal number $\eta$, both outcomes $0$ and $\eta$ have $|\delta| = 1$. The other form, which rounds up or down with probability $1/2$ each, is not unbiased.

## Depends on

- [Binary floating-point numbers](../../floating-point-rounding/is-float.md)

## Sources

- M. P. Connolly, N. J. Higham and T. Mary, "Stochastic rounding and its probabilistic backward error analysis", *SIAM J. Sci. Comput.* 43(1):A566–A585, 2021; MIMS EPrint 2020.12, Section 1, definitions (1.1) (mode 1) and (1.2) (mode 2, the form used here), and Section 2, the bounds (2.4a)–(2.4b). <https://eprints.maths.manchester.ac.uk/2763/1/paper.pdf>
