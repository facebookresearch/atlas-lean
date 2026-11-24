# Homomorphism density

For a simple graph $F$ on a finite vertex set $\alpha$ and a weighted graph $w : \operatorname{Sym}^2 V \to \mathbb R$ on a finite vertex set $V$ (unit node weights, real edge weights, loops allowed),

$$t(F, w) = \frac{1}{|V|^{|\alpha|}} \sum_{\varphi : \alpha \to V} \prod_{ij \in E(F)} w(\varphi(i), \varphi(j)).$$

If $\alpha$ is empty, $t(F, w) = 1$; if $\alpha$ is nonempty and $V$ is empty, there are no maps and $t(F, w) = 0/0$ is read as $0$. For the $0/1$ weight of a simple graph $G$ with at least one vertex, $t(F, w)$ is the probability that a uniformly random map $V(F) \to V(G)$ is a homomorphism, and it equals $\hom(F, G) / |V(G)|^{|V(F)|}$.

A sequence of graphs with nonempty vertex sets converges when $t(F, \cdot)$ converges for every $F$; the limit object is a graphon, whose densities are given by an integral instead of a sum.

## Background

- [Homomorphism density in a graphon](graphon-hom-density.md): the same quantity with the sum over maps replaced by an integral over $[0,1]^k$.
- [Homomorphism density counts homomorphisms](hom-density-adj-weight.md): the identity $t(F, G) = \hom(F, G) / |V(G)|^{|V(F)|}$ for simple graphs.

## Sources

- L. Lovász and B. Szegedy, "Limits of dense graph sequences", *J. Combin. Theory Ser. B* 96 (2006), 933–957, arXiv:math/0408173, §2.1 (definition of $\hom(F, G)$, equation (2), and $t(F, G)$).
- C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing", *Adv. Math.* 219 (2008), 1801–1851, arXiv:math/0702004, §2.2, equations (2.2)–(2.3).
