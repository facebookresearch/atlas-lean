# Generalized median voter scheme on an interval

A *generalized median voter scheme* on a closed interval $[a, b]$ for a finite nonempty agent set $\iota$ is given by phantom parameters $\alpha_S \in [a, b]$ for coalitions $S \subseteq \iota$, antitone in $S$, with $\alpha_\emptyset = b$ and $\alpha_\iota = a$. It maps reported peaks $x$ to $\min_S \max\bigl(\alpha_S, \max_{i \in S} x_i\bigr)$ (with $\max_{i \in \emptyset} x_i = a$). With $n - 1$ sorted phantom points $y_1 \le \dots \le y_{n-1}$, taking $\alpha_S = y_{n - |S|}$ for $1 \le |S| \le n-1$ gives the *phantom median* rule, the median of the $n$ peaks and the $n - 1$ phantoms.

## Depends on

- [Facility-location mechanism on a metric space](facility-location-mechanism-on-a-metric-space.md)
- [Single-peaked profile](../../social-choice/voting-rules-and-majority-relations/black-s-median-voter-theorem/single-peaked-profile.md)

## Sources

- Herve Moulin, "On Strategy-Proofness and Single Peakedness", Public Choice, 1980.
- James Schummer and Rakesh V. Vohra, "Mechanism Design without Money", Algorithmic Game Theory, Cambridge University Press, 2007.
