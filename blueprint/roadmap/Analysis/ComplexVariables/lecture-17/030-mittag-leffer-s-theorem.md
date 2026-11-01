---
article_id: af_c3488c0beab146dad3aebb59
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MittagLeffler.mittag_leffler
---

# Theorem 1 (Mittag-Leffer's Theorem)

Let $\{b_{\nu}\}$ be a sequence in $\mathbb{C}$ such that $\lim_{\nu \to \infty} b_{\nu} = \infty$ and $P_{\nu}(\zeta)$ polynomials without constant term. Then there exist functions $f$ meromorphic in $\mathbb{C}$ with poles at just the points $b_{\nu}$ and corresponding singular parts $P_{\nu}\!\left(\frac{1}{z - b_{\nu}}\right)$. The most general $f(z)$ of this kind can be written $$f(z) = g(z) + \sum_{\nu} \left[ P_{\nu}\!\left(\frac{1}{z - b_{\nu}}\right) - p_{\nu}(z) \right]$$ where $g$ is holomorphic in $z$ and the $p_{\nu}$ are polynomials.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 1 (Taylor's Theorem)](../lecture-10/012-taylor-s-theorem.md)

## Sources

- [MIT 18.112 Functions of a Complex Variable (Fall 2008), Lecture 17: Mittag-Leffer's Theorem](../../../../sources/v1/ComplexVariables.md)
