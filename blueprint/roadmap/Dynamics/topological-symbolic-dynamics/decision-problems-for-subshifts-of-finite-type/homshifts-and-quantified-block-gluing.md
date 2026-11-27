# Homshifts and quantified block gluing

The homshift of a finite graph is the subshift of finite type of all graph homomorphisms from the grid into that graph; quantified block gluing measures how far apart two square patterns must be placed before they always occur together in one configuration.

**Homshifts.** Let $G$ be a finite undirected graph, possibly with self-loops, and $d \ge 1$. View $\mathbb{Z}^d$ as the grid graph, in which two points are adjacent when they differ by $1$ in exactly one coordinate. The *$d$-dimensional homshift* of $G$ is

$$
X^d_G = \{ x \in V_G^{\mathbb{Z}^d} : (x_{\mathbf{u}}, x_{\mathbf{v}}) \in E_G \text{ for all adjacent } \mathbf{u}, \mathbf{v} \in \mathbb{Z}^d \},
$$

the set of graph homomorphisms from the grid to $G$; it is a nearest-neighbor $\mathbb{Z}^d$-subshift of finite type whose constraint is the same in every direction. The homshift is transitive exactly when $G$ is connected, and topologically mixing exactly when $G$ is connected and not bipartite.

**Quantified block gluing.** For $\mathbb{U}, \mathbb{U}' \subseteq \mathbb{Z}^d$ let $\delta(\mathbb{U}, \mathbb{U}') = \min_{\mathbf{u} \in \mathbb{U}, \mathbf{u}' \in \mathbb{U}'} \|\mathbf{u} - \mathbf{u}'\|_\infty$. For $f\colon \mathbb{N}^* \to \mathbb{N}$ and $k \in \mathbb{N}^*$, a $\mathbb{Z}^d$-subshift $X$ is *$(f, k)$-phased block gluing* if for every two globally admissible patterns $p, p'$ on cubes of the same side $n$ and every $\mathbf{u}, \mathbf{u}' \in \mathbb{Z}^d$ with

$$
\delta\bigl(\mathbf{u} + [\![0, n-1]\!]^d, \ \mathbf{u}' + [\![0, n-1]\!]^d\bigr) \ge f(n),
$$

there are $x \in X$ and $\mathbf{v} \in \mathbb{Z}^d$ with $\|\mathbf{v}\|_\infty < k$, $x|_{\mathbf{u} + [\![0, n-1]\!]^d} = p$ and $x|_{\mathbf{u}' + \mathbf{v} + [\![0, n-1]\!]^d} = p'$. It is *$f$-block gluing* if it is $(f, 1)$-phased block gluing. For a function $g$, $X$ is *$\Theta(g)$-block gluing* (respectively *$O(g)$-block gluing*) if it is $f$-block gluing for some $f \in \Theta(g)$ (respectively $f \in O(g)$), and similarly for phased block gluing.

## Depends on

- [Subshifts of finite type on a finitely generated group and the domino problem](subshifts-of-finite-type-on-groups.md)

## Proof depends on

None.

## Expansion

Every homshift $X^d_G$ with $d > 1$ is $O(n)$-phased block gluing, and for non-bipartite $G$ it is $f$-block gluing exactly when it is $f$-phased block gluing (Lemmas 2.7 and 2.8 of the source). Gangloff, Hellouin de Menibus and Oprocha showed that a two-dimensional homshift is either $\Theta(n)$-phased block gluing or $O(\log n)$-phased block gluing, according to whether its square cover is infinite or finite. Many properties of homshifts are decidable: a homshift is non-empty as soon as $G$ has an edge, a pattern extends to a full configuration if and only if it extends to a rectangle, and the topological entropy is computable.

## Sources

- N. Chandgotia, S. Gangloff, B. Hellouin de Menibus and P. Oprocha, "Undecidability of the block gluing classes of homshifts", Nonlinearity 39 (2026), no. 8, article 085011, https://doi.org/10.1088/1361-6544/ae73db; read in arXiv:2507.21342v2 (the introduction, the notation for homshifts, Definitions 2.5 and 2.6 and Lemmas 2.7 and 2.8 of arXiv:2507.21342v2).
