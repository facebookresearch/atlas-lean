# Laplace distribution

For real $m$ and $b$, the Laplace law $\mathrm{Lap}(m, b)$ is the measure on $\mathbb{R}$ with density
$z \mapsto \max\bigl(\exp(-|z - m| / b) / (2b), 0\bigr)$ with respect to Lebesgue measure. For $b > 0$ the
density is $\exp(-|z - m| / b) / (2b)$ and $\mathrm{Lap}(m, b)$ is a probability law with location $m$
and scale $b$. For $b \le 0$ the measure is $0$: for $b < 0$ the formula is negative, and for $b = 0$
it reads $\exp(0)/0 = 0$ with division by zero read as $0$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Definition 3.2.
