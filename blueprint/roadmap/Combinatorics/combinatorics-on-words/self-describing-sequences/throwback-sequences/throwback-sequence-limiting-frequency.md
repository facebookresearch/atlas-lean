# Limiting frequencies in throwback sequences

Let $X = (x_0, x_1, \dots)$ be a sequence of
pairwise distinct positive integers with throwback sequence $T(X) = (t_0, t_1, \dots)$, and for a
natural number $w$ let $\sigma(w)$ be the number of indices $i$ with $x_i < w$. Then for every
index $j$, writing $x = x_j$, the number of $k < N$ with $t_k = x$, divided by $N$, converges as
$N \to \infty$ to

$$f(x) = \frac{1}{x - \sigma(x) + 1} \prod_{w} \frac{w - \sigma(w)}{w - \sigma(w) + 1},$$

where the product runs over the values $w < x$ taken by $X$.

For a term $w$ of $X$, $\sigma(w)$ is the index of $w$ in the increasing rearrangement of $X$.

## Sources

- Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*, Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 4 (`jis-2025-25.5.1-thm-4`).
