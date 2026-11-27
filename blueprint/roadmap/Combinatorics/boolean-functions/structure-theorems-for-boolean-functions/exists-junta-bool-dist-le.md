# Friedgut's junta theorem, explicit form

Let $f : \{-1, 1\}^n \to \{-1, 1\}$ and $\varepsilon > 0$. There are a set $J$ of coordinates with

$$|J| \le \frac{\mathbf{I}[f]^3\; 9^{\lceil \mathbf{I}[f]/\varepsilon \rceil}}{\varepsilon^2}$$

and a Boolean function $h$ depending only on the coordinates in $J$ with
$\mathrm{dist}(f, h) \le 2\varepsilon$.

Take $k = \lceil \mathbf{I}[f]/\varepsilon \rceil$, so that the weight above degree $k$ is at most
$\varepsilon$, and the spectral part of Friedgut's argument. Then
$\|f - f^{\subseteq J}\|_2^2 = \sum_{S \not\subseteq J} \hat f(S)^2 \le 2\varepsilon$, where
$f^{\subseteq J} = \sum_{S \subseteq J} \hat f(S) \chi_S$, and $h = \mathrm{sgn}(f^{\subseteq J})$ is
$2\varepsilon$-close to $f$. When $\mathbf{I}[f] = 0$, $f$ is constant and $J = \emptyset$. The source
sharpens $2\varepsilon$ to $\varepsilon$ with Exercise 3.34.

## Sources

- E. Friedgut, "Boolean functions with low average sensitivity depend on few coordinates",
  *Combinatorica* 18 (1998), 27–35.
- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Theorem 9.28 (second part) with Proposition 3.2 and Proposition 3.31.
