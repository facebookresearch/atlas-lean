# Expected rounds to assemble a genomic word under parallel selection

**Model.** A target word has $L$ letters from an alphabet of $K \ge 2$ letters. In each round, every position that is still incorrect is re-guessed independently and uniformly at random; a position guessed correctly is kept forever (selection retains beneficial mutations at each site). Blind search, which re-guesses the whole word each round, needs $K^L$ rounds on average.

**Theorem.** Let $T_L$ be the number of rounds until all $L$ letters are correct. As $L \to \infty$,

$$\mathbb E[T_L] = \frac{\log L}{\log\frac{K}{K-1}} + \beta(L) + O(L^{-1}),$$

where, with $X = K/(K-1)$ and Euler's constant $\gamma$,

$$\beta(L) = \frac12 + \frac{\gamma}{\log X} + \frac{2}{\log X}\sum_{k\ge1}\operatorname{Re}\Big(\Gamma\big(-1 - \tfrac{2\pi i k}{\log X}\big)\,e^{2\pi i k\log_X L}\,\frac{2\pi i k}{\log X}\Big)$$

is a periodic function of $\log L$. Its oscillating part is tiny: for every $K \ge 2$ it deviates from the constant $\frac12 + \gamma/\log X$ by at most $2\times10^{-6}$.

Since $\log\frac{K}{K-1} \approx 1/K$ for large $K$, the expected number of rounds is about $K\log L$, rather than $K^L$.

## Expansion

Each position is fixed at an independent geometric time with success probability $1/K$, so $T_L$ is the maximum of $L$ i.i.d. geometric variables and $\mathbb P(T_L \le t) = (1 - (1 - 1/K)^t)^L$. Then $\mathbb E[T_L] = \sum_{t\ge0}\big(1 - (1 - X^{-t})^L\big)$, a classical sum whose asymptotics are obtained by Mellin transform: the double pole at $s = 0$ gives $\log_X L + \frac12 + \gamma/\log X$, and the poles at $s = 2\pi i k/\log X$ give the periodic fluctuations with coefficients involving $\Gamma$ on the imaginary axis, which decay so fast that the oscillation has amplitude of order $10^{-6}$.

## Sources

- Herbert S. Wilf and Warren J. Ewens, *There's plenty of time for evolution*, Proc. Natl. Acad. Sci. USA 107(52) (2010), 22454–22456. <https://doi.org/10.1073/pnas.1016207107> Theorem 1 and the formula for $\beta(L)$. Locators use the numbering of the preprint arXiv:1010.5178.
