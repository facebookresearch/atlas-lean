# Airy limits of leaf-to-root and unary-node-to-root distances in plane trees

**Setting.** Use the plane tree model of RNA secondary structure and the Gibbs law of the nearest neighbor thermodynamic model from [Gibbs scaling of ladder distances under the nearest neighbor thermodynamic model](gibbs-scaling-of-ladder-distances-under-the-nearest-neighbor-thermodynamic-model.md): a tree $T$ with $n$ edges has energy $E(T)=\alpha d_0(T)+\beta d_1(T)+\gamma r(T)$, where $d_0$ counts leaves (childless non-root vertices) and $d_1$ unary non-root vertices. Let $\mathcal{P}^{LR}(T)$ be the sum of the root distances of all leaves, $\mathcal{P}^{IR}(T)$ the sum of the root distances of all unary vertices, and $\mathcal{P}^{PL}(T)$ the sum of root distances of all vertices. Let $\rho=e^{-\alpha}+e^{-\beta}+2e^{-\alpha/2}$ and let $A=\int_0^1 e(t)\,dt$ be the Airy-distributed area of a normalized Brownian excursion.

**Theorem.**

1. (Uniform trees.) For $T$ uniform on the $n$-edge plane trees, as $n\to\infty$,

$$\frac{\mathcal{P}^{PL}}{\sqrt{2n^3}}\xrightarrow{d}A,\qquad 2\,\frac{\mathcal{P}^{LR}}{\sqrt{2n^3}}\xrightarrow{d}A,\qquad 4\,\frac{\mathcal{P}^{IR}}{\sqrt{2n^3}}\xrightarrow{d}A.$$

2. (Gibbs trees.) For all $\alpha,\beta,\gamma\in\mathbb{R}$ and root degree bounded by any fixed $h$ (or unrestricted with $\gamma=0$),

$$\frac{\mathcal{P}^{LR}}{\sqrt{2n^3}}\xrightarrow{d}\frac{e^{-\alpha/4}}{\sqrt{\rho}}\,A,\qquad \frac{\mathcal{P}^{IR}}{\sqrt{2n^3}}\xrightarrow{d}\frac{e^{-\beta}}{\sqrt{\rho}\,e^{-\alpha/4}\,(e^{-\alpha/2}+1)}\,A.$$

At $\alpha=\beta=0$ the constants are $1/2$ and $1/4$, matching part 1: about half of the vertices are leaves and a quarter are unary, and they sit at typical depth.

## Expansion

Leaf and unary root distances are, up to $O(n)$, *simple* subtree additive properties: $\mathcal{P}^{LR}(T)=\sum_{v\ne\mathrm{root}} d_0(T_v)+O(n)$ and $\mathcal{P}^{IR}(T)=\sum_{v\ne\mathrm{root}} d_1(T_v)+O(n)$, induced by the additive properties $d_0$ and $d_1$. The comparison theorem for simple subtree additive properties says that if two bounded-toll additive properties have power sums agreeing up to a factor $\mu^m$ and an error $O(n^{(2m-4)/2}4^n)$, then the induced subtree additive properties, scaled by $n^{3/2}$, have limits differing by the factor $\mu$. Since $d_0(T)/n\to1/2$ and $d_1(T)/n\to1/4$ in this sense while $\mathcal{P}^{PL}$ is induced by the vertex count, part 1 follows from Takács' Airy limit for path length. Part 2 applies the Gibbs-to-uniform translation theorem with $f=p$ (leaf count) and $f=q$ (unary count).

## Depends on

- [Gibbs scaling of ladder distances under the nearest neighbor thermodynamic model](gibbs-scaling-of-ladder-distances-under-the-nearest-neighbor-thermodynamic-model.md)

## Sources

- Anna Kirkpatrick, Chidozie Onyeze, "On the Asymptotic Distributions of Classes of Subtree Additive Properties of Plane Trees under the Nearest Neighbor Thermodynamic Model", arXiv:2101.04714 (2021): Section "The Distributions of Simple Subtree Additive Properties" (main comparison theorem, its corollary and the leaf/internal-node-to-root corollary) and the leaf-to-root and internal-node-to-root corollary of the NNTM section. <https://doi.org/10.48550/arXiv.2101.04714>
