# Counting reduced unicellular hypermonopoles by genus

Fix $g \in \mathbb{N}$. For
each $n \in \mathbb{N}$ let $\zeta_n$ be the cyclic permutation of $\{0, \ldots, n - 1\}$
sending $i$ to $i + 1$ modulo $n$, and let $z(\pi)$ be the number of cycles of a permutation
$\pi$, fixed points included. Let $U_g$ be the set of pairs $(n, \alpha)$, with
$n \in \mathbb{N}$ and $\alpha$ a permutation of $\{0, \ldots, n - 1\}$, such that
$z(\zeta_n) = 1$, $z(\alpha^{-1} \zeta_n) = 1$ (the product applies $\zeta_n$ first), $\alpha$
has no fixed point, and $n + 2 = z(\zeta_n) + z(\alpha) + z(\alpha^{-1} \zeta_n) + 2g$. Then
$U_g$ is finite and its number of elements is $\sum_{n = 2g + 1}^{4g} r(n, n - 2g)$, where
$r(n, k)$ is the number of permutations $\alpha$ of $\{0, \ldots, n - 1\}$ without fixed
points such that $z(\alpha^{-1} \zeta_n) = 1$ and $z(\alpha) = k$.

The pairs in $U_g$ are the reduced unicellular hypermonopoles $(\zeta_n, \alpha)$ of genus
$g$, with the genus given by Jacques' formula and the vertex permutation normalized to
$\zeta_n$. The paper writes $u(g)$ for the number of elements of $U_g$; its first value is
$u(1) = 2$.

## Sources

- Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of Integer Sequences 28 (2025), Article 25.3.3, Proposition 15 (`jis-2025-25.3.3-prop-15`).
