# Quantified block gluing

Quantified block gluing measures how far apart two cube patterns of a $\mathbb{Z}^d$-subshift must be placed before they always occur together in one configuration; the block-gluing rate of a subshift is the optimal order of growth of that distance.

For $\mathbb{U}, \mathbb{U}' \subseteq \mathbb{Z}^d$ let $\delta(\mathbb{U}, \mathbb{U}') = \min_{\mathbf{u} \in \mathbb{U}, \mathbf{u}' \in \mathbb{U}'} \|\mathbf{u} - \mathbf{u}'\|_\infty$. For $f\colon \mathbb{N}^* \to \mathbb{N}$ and $k \in \mathbb{N}^*$, a [subshift](subshifts-of-finite-type-on-groups.md) $X$ of $A^{\mathbb{Z}^d}$ is *$(f, k)$-phased block gluing* if for every two globally admissible patterns $p, p'$ on cubes of the same side $n$ and every $\mathbf{u}, \mathbf{u}' \in \mathbb{Z}^d$ with

$$
\delta\bigl(\mathbf{u} + [\![0, n-1]\!]^d, \ \mathbf{u}' + [\![0, n-1]\!]^d\bigr) \ge f(n),
$$

there are $x \in X$ and $\mathbf{v} \in \mathbb{Z}^d$ with $\|\mathbf{v}\|_\infty < k$, $x|_{\mathbf{u} + [\![0, n-1]\!]^d} = p$ and $x|_{\mathbf{u}' + \mathbf{v} + [\![0, n-1]\!]^d} = p'$. It is *$f$-block gluing* if it is $(f, 1)$-phased block gluing, and *$f$-phased block gluing* if it is $(f, k)$-phased block gluing for some $k$.

Gluing at gap $f$ implies gluing at every gap $f' \ge f$, since the condition only constrains pairs at distance at least $f(n)$. So the classes are read by their optimal order. For a function $g$, $X$ is *$O(g)$-block gluing* (respectively *$o(g)$-block gluing*) if it is $f$-block gluing for some $f \in O(g)$ (respectively $f \in o(g)$), and $X$ has *block-gluing rate $\Theta(g)$* if it is $O(g)$-block gluing but not $o(g)$-block gluing; the same terms are used for phased block gluing. Definition 2.6 of the source states the $\Theta(g)$ class as "$f$-block gluing for some $f \in \Theta(g)$"; its proof of Theorem 1.2 and its Section 6.2.2 use the optimal-order reading given here.

## Depends on

- [Subshifts of finite type on a finitely generated group](subshifts-of-finite-type-on-groups.md)

## Proof depends on

None.

## Sources

- N. Chandgotia, S. Gangloff, B. Hellouin de Menibus and P. Oprocha, "Undecidability of the block gluing classes of homshifts", Nonlinearity 39 (2026), no. 8, article 085011, https://doi.org/10.1088/1361-6544/ae73db; read in arXiv:2507.21342v2 (Definitions 2.5 and 2.6, the proof of Theorem 1.2 in Section 5 and Section 6.2.2 of arXiv:2507.21342v2).
