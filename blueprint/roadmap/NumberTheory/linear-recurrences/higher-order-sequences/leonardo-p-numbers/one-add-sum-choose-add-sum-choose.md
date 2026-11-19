# Schütz–Kelly binomial sum identity

For all natural numbers $J$, $n$ and $p$,

$$1 + \sum_{i=0}^{J} \binom{\max(n-pi,\,0)}{i+1} + \sum_{i=0}^{J-1} \binom{\max(n-pi-p,\,0)}{i+1} =
\sum_{i=0}^{J} \binom{\max(n-pi,\,0)+1}{i+1}.$$

Truncating the upper indices at $0$ makes a negative upper index give $\binom{0}{i+1} = 0$,
matching the paper's binomials. The identity holds for all natural numbers $J$, $n$, $p$,
including the value $0$, which lies outside the paper's positive range.

## Sources

- Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized Leonardo $p$-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2, Lemma 6.
