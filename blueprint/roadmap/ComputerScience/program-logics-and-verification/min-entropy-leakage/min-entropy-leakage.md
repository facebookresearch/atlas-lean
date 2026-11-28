# Min-entropy leakage

Let $X$ be a finite nonempty type of secrets, $Y$ a finite type of observations, $\pi$ a prior on $X$ and $C : X \to \mathrm{PMF}(Y)$ a channel. The min-entropy leakage is the binary logarithm of posterior over prior vulnerability:

$$\mathcal{L}(\pi, C) = \log_2 \frac{V(\pi, C)}{V(\pi)},$$

with the real conventions $x / 0 = 0$ and $\log_2 0 = 0$.

## Sources

- G. Smith, *On the Foundations of Quantitative Information Flow*, FoSSaCS 2009.
