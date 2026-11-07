# Growing from an iterate of $\tau_k$ gives an iterate of $\tau_k$

Let $\tau_k$ be the
substitution sending the letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, extended
letterwise to words, and let $\mathrm{grow}_{k,n}^f(w)$ be the word obtained from $w$ by applying
$\tau_k$ until it has more than $n$ letters, at most $f$ times. For all $k, n, f, j$ there is an
$m$ with $\mathrm{grow}_{k,n}^f(\tau_k^j(k)) = \tau_k^m(k)$ such that $\tau_k^m(k)$ has more than
$n$ letters or $j + f \le m$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Section 1.2 (prefixes `τ_k^j(k)` of `x_k`).
