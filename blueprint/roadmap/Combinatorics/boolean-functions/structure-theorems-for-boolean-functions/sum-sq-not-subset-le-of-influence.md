# Spectral part of Friedgut's argument

Let $f : \{-1, 1\}^n \to \{-1, 1\}$ with $\mathbf{I}[f] > 0$, let $\varepsilon > 0$ and $k \in \mathbb{N}$,
and put

$$\tau = \frac{\varepsilon^2}{\mathbf{I}[f]^2\, 9^k}, \qquad J = \{j : \mathrm{Inf}_j[f] \ge \tau\}.$$

Then $\sum_{|S| \le k,\ S \not\subseteq J} \hat f(S)^2 \le \varepsilon$: the Fourier spectrum of $f$
is $\varepsilon$-concentrated on $\{S : S \subseteq J\} \cup \{S : |S| > k\}$.

The proof sums Corollary 9.12, in the form $\sum_{S \ni j} 3^{-|S|} \hat f(S)^2 \le
\tfrac13 \mathrm{Inf}_j[f]^{3/2} \le \mathrm{Inf}_j[f]^{3/2}$, over the coordinates $j \notin J$: the left side counts every set that leaves $J$ with weight at least
$3^{-k}$, and the right side is at most $\sqrt\tau\, \mathbf{I}[f] = 3^{-k} \varepsilon$.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Theorem 9.28 (first part).

## Informally uses

- [Corollary 9.12: stable influences of Boolean functions](stable-influence-third-le.md): the
  source's proof sums this bound over the coordinates of small influence.
