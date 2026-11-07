# Iterates of the Hofstadter substitution on the letter $k$

Let $k \ge 1$, let $\tau_k$ be
the morphism of finite words over $\mathbb{N}$ that replaces the letter $k$ by the word $k\,1$ and
every other letter $i$ by $i + 1$, and write $\tau_k^j(k)$ for the word obtained by applying
$\tau_k$ $j$ times to the one-letter word $k$. For every natural number $j$: if $j \le k$, then
$\tau_k^j(k) = k\,1\,2 \cdots j$, the letter $k$ followed by $1, 2, \dots, j$; and if $j \ge k$,
then $\tau_k^j(k)$ is the concatenation $\tau_k^{j-1}(k)\,\tau_k^{j-k}(k)$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Proposition 3 (`jis-2026-26.3.3-prop-3`).
