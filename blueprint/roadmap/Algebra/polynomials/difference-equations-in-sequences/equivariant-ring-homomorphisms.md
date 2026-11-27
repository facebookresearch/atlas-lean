# Equivariant semiring homomorphisms

For monoids acting on two semirings by semiring endomorphisms, an equivariant semiring homomorphism along a monoid homomorphism is a semiring homomorphism that carries the action on the first semiring to the action on the second.

Let $M$ and $N$ be monoids, $\varphi \colon M \to N$ a monoid homomorphism, and $R$ and $S$ semirings with actions of $M$ on $R$ and of $N$ on $S$ by [semiring endomorphisms](monoid-actions-on-rings.md). A $\varphi$-equivariant semiring homomorphism $f \colon R \to S$ is a map with $f(0) = 0$, $f(1) = 1$, $f(r + s) = f(r) + f(s)$ and $f(rs) = f(r) f(s)$ for all $r, s \in R$, and $f(m \cdot r) = \varphi(m) \cdot f(r)$ for all $m \in M$ and $r \in R$.

For $N = M$ and $\varphi$ the identity, these are the morphisms of $M$-rings of difference algebra: ring homomorphisms that commute with the actions.

## Sources

- Gleb Pogudin, Thomas Scanlon and Michael Wibmer, *Solving difference equations in sequences: universality and undecidability*, Forum of Mathematics, Sigma 8 (2020), e33, https://doi.org/10.1017/fms.2020.14; read in arXiv:1909.03239v2, Definition 2.6 of Section 2 (morphisms of $M$-rings).
