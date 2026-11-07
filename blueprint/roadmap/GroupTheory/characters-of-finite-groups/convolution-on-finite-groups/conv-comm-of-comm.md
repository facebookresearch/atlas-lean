# Convolution on a finite abelian group is commutative

Let $G$ be a finite abelian group and
write $f \ast g$ for the convolution $(f \ast g)(x) = \sum_{y \in G} f(y)\, g(y^{-1} x)$ of
functions on $G$. For all $f, g : G \to \mathbb{C}$ we have $f \ast g = g \ast f$.

Proof: Reindex by $y \mapsto y^{-1} x$ and use commutativity in $G$ and in $\mathbb{C}$,
as in the commutative group-algebra argument in Terras, Ch. 2.

## Sources

- `undergrad.yaml`, section "Representation theory of finite groups", entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 2 (commutative group algebra of an abelian group).
