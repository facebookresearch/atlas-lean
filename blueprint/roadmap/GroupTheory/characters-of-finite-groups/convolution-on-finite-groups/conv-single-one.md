# The delta function at the identity is a left unit for convolution

Let $G$ be a finite group,
write $f \ast g$ for the convolution $(f \ast g)(x) = \sum_{y \in G} f(y)\, g(y^{-1} x)$ of
functions on $G$, and let $\delta_1 : G \to \mathbb{C}$ be given by $\delta_1(1) = 1$ and
$\delta_1(x) = 0$ for $x \neq 1$. Then $\delta_1 \ast f = f$ for every $f : G \to \mathbb{C}$.

Proof: Expand the convolution and collapse the sum at the unique nonzero value
of the delta function, following the identity-element argument in Terras, Ch. 1.

## Sources

- `undergrad.yaml`, section "Representation theory of finite groups", entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 1 (identity of the group algebra).
