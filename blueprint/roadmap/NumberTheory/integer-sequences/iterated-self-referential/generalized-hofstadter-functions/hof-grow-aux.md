# Bounded growth of a word under $\tau_k$

Let $\tau_k$ be the substitution sending the
letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, extended letterwise to words. Given
$n$, a bound $f$ and a word $w$, the result is $w$ if $f = 0$ or $w$ has more than $n$ letters,
and otherwise it is the result for the bound $f - 1$ and the word $\tau_k(w)$. Thus $\tau_k$ is
applied to $w$ until the word has more than $n$ letters, at most $f$ times.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Section 1.2 (prefixes `τ_k^j(k)` of `x_k`).
