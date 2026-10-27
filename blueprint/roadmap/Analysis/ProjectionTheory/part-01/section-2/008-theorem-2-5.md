---
article_id: af_0b42d19cba9934b411f9735f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: FourierFF.fourier_inversion
---

# Theorem 2.5

If $f \colon \mathbb{F}_q^d \to \mathbb{C}$, then $$f(x) = \frac{1}{q^d} \sum_{\xi \in \mathbb{F}_q^d} \hat{f}(\xi) e(x \cdot \xi) = \underbrace{\frac{1}{q^d} \hat{f}(0)}_{f_0(x)} + \underbrace{\frac{1}{q^d} \sum_{\xi \neq 0} \hat{f}(\xi) e(x \cdot \xi)}_{f_h(x)}.$$

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.156 Projection Theory (Spring 2025), Section 2, Subsection 2.2](../../../../../sources/v1/ProjectionTheory.md)
