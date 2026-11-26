# Lower bounding function for the maximal frequency given homozygosity

For a real number $J$, let $c = \lceil 1/J \rceil$ be the integer ceiling of $1/J$. The function $M_{\min}$ is

$$M_{\min}(J) = \frac{1}{c} \left( 1 + \sqrt{\frac{c J - 1}{c - 1}} \right).$$

Here $1/0 = 0$ and $x/0 = 0$, and $\sqrt{x} = 0$ for $x < 0$. For a probability vector with homozygosity $J = \sum_i p_i^2$, $M_{\min}(J)$ is the lower bound for the largest entry.

## Sources

- Bradley K. Moon and Noah A. Rosenberg, "Integer Sequences for Diversity Statistics", Journal of Integer Sequences 29 (2026), Article 26.1.5, Eq. (1).
