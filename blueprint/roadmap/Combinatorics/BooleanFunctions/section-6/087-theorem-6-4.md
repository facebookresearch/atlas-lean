---
article_id: af_899d212d83d6c2c31ac7b823
declaration: theorem
origin: cited
lean: BooleanFourier.majority_is_stablest_real_valued
---

# Theorem 6.4

For all $\varepsilon > 0$, $\rho \in (0,1)$ there are $d \in \mathbb{R}$ and $\tau > 0$ such that if $f \colon \{-1,1\}^n \to [-1,1]$ is balanced and $\max_i I_i[f^{\leqslant d}] \leqslant \tau$, then $\operatorname{Stab}_{\rho}(f) \leqslant 1 - \frac{2}{\pi} \operatorname{Arccos}(\rho) + \varepsilon$.

## Depends on

- [Definition 2.2 (Lecture 4, Section 2)](../lecture-4/007-definition-2-2.md)
- [Definition 1.1 (Noise Stability)](../section-1/052-noise-stability.md)

## Proof depends on

- [Theorem 5.3](../section-5/083-theorem-5-3.md)
- [Definition 6.1](084-definition-6-1.md)
- [Definition 6.2](085-definition-6-2.md)
- [Theorem 6.3 (Borel's theorem)](086-borel-s-theorem.md)

## Sources

- [MIT 18.218 Analysis of Boolean Functions (Spring 2021), Section 6](../../../../sources/v1/BooleanFunctions.md)
