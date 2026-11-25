# Girstmair's cotangent power coefficients

For natural numbers $r$ and $j$, the rational
number $c_{r,j}$ is

$$c_{r,j} = (-1)^{r-1} \sum_{k=j}^{r} \frac{(-2)^{k-j}}{(k-1)!} \binom{r}{k} S(k, j),$$

where $S(k, j)$ is the unsigned Stirling number of the first kind, the number of permutations
of $k$ elements with exactly $j$ cycles. Subtraction of natural numbers is truncated at $0$: for
$r = 0$ the exponent $r - 1$ is read as $0$, and for $j = 0$ the factor $(k-1)!$ of the term
$k = 0$ is read as $0! = 1$.

These coefficients express $(i \cot)^r$ in terms of the derivatives $i^j \cot^{(j-1)}$.

## Sources

- Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025), Article A63, Equation (8). The equation is not in the journal record; it is read from the arXiv version, arXiv:2504.08330, Section 3, where it also follows from the displayed derivation.
