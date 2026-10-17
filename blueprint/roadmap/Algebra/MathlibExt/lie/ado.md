---
article_id: af_e2814c85730971c9d127682d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Algebra.Lie.LandmarkWanted.ado
---

# Ado

Every finite-dimensional Lie algebra `L` over a field `K` of characteristic zero admits a faithful
finite-dimensional representation `ρ : L →ₗ⁅K⁆ Module.End K (Fin n → K)` that is injective.

Proof: Following Tao's 2011 route, the nilpotent and solvable cases are proved by induction using
finite-dimensional quotients of universal enveloping algebras. The general case uses the Levi
decomposition and combines the resulting radical representation with the adjoint representation.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Levi decomposition](levi-decomposition/levi-decomposition.md)

## Sources

- [MathlibExt, MathlibExt.Algebra.Lie.Ado](../../../../sources/v2/MathlibExt.md)
- I. D. Ado, Bull. Soc. Phys.-Math. Kazan 7 (1935) and 1947 char-zero theorem; Bourbaki, Lie Groups and Lie Algebras; Lean states char-zero finite-dimensional version while modern theorem extends to arbitrary fields.
