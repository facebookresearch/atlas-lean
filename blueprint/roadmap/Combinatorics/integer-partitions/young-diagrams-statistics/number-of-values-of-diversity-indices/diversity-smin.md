# Lower bounding function for the Shannon index given the maximal frequency

For a real number $M$, let $f = \lfloor 1/M \rfloor$ be the integer floor of $1/M$. The function $S_{\min}$ is

$$S_{\min}(M) = f M \log \frac{1}{M} + (1 - f M) \log \frac{1}{1 - f M}.$$

Here $\log$ is the natural logarithm with $\log 0 = 0$ and $\log x = \log |x|$ for $x < 0$, and $1/0 = 0$ and $x/0 = 0$. The argument $1/(1 - fM)$ of the second logarithm is the one used in Proposition 2 of the source; its Eq. (3) misplaces a floor bracket.

## Sources

- Bradley K. Moon and Noah A. Rosenberg, "Integer Sequences for Diversity Statistics", Journal of Integer Sequences 29 (2026), Article 26.1.5, Eq. (3) and Proposition 2.
