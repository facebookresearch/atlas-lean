---
article_id: af_2b5570912e85d2162db47cb5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: EllipsoidMethod.ellipsoid_volume_ratio_le_exp
---

# Lemma 1 (volume contraction of the ellipsoid update)

Let $D$ be a positive-definite $n \times n$ matrix, $z \in \mathbb{R}^n$, and $a \in \mathbb{R}^n$ nonzero, and let $\operatorname{Ell}(D, z) = \{x \mid (x - z)^\top D^{-1} (x - z) \leq 1\}$. The minimum-volume ellipsoid containing the half-ellipsoid $\operatorname{Ell}(D, z) \cap \{x \mid a \cdot x \leq a \cdot z\}$ is the ellipsoid $E' = \operatorname{Ell}(D', z')$ with $$z' = z - \frac{1}{n+1} \frac{Da}{\sqrt{a^\top D a}}$$ and $$D' = \frac{n^2}{n^2 - 1} \left( D - \frac{2}{n+1} \frac{Da\, a^\top D}{a^\top D a} \right).$$ Moreover $\operatorname{vol}(E') / \operatorname{vol}(E) \leq e^{-1/(2n+2)}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.433 Combinatorial Optimization (Fall 2003), The Ellipsoid Algorithm, Oct 30 - Nov 4](../../../../sources/v1/CombinatorialOptimization.md)
