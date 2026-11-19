# Biorthogonal dual of a Riesz basis

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $E$ be a Hilbert space over $\mathbb{K}$ with a Hilbert basis $(b_i)_{i \in \iota}$, and let $(f_i)_{i \in \iota}$ be a [Riesz basis](is-riesz-basis.md) with respect to $(b_i)$. Then there is a biorthogonal dual family $(g_j)_{j \in \iota}$ in $E$, with $\langle f_i, g_j \rangle = 1$ if $i = j$ and $0$ otherwise, and the reconstruction formula

$$
x = \sum_{i \in \iota} \langle g_i, x \rangle\, f_i
$$

holds for every $x \in E$, the series converging unconditionally. One can take $g_j = (T^{-1})^* b_j$, where $T$ is a bounded invertible operator with $T b_i = f_i$.
