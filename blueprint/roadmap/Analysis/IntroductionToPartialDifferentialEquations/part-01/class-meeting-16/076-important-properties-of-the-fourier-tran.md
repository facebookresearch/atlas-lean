---
article_id: af_034cb752deafd2c049991c8c
declaration: theorem
origin: cited
lean: FourierAnalysis.fourier_transform_properties
---

# Theorem 2.1 (Important properties of the Fourier transform)

Assume that $f, g \in L^{1}(\mathbb{R}^{n})$, and let $t \in \mathbb{R}$. Then:
(a) $(\tau_{y} f)^{\wedge}(\xi)=e^{-2 \pi i \xi \cdot y} \hat{f}(\xi)$
(b) $\hat{h}(\xi)=\tau_{\eta} \hat{f}(\xi)$ if $h(x) \coloneqq e^{2 \pi i \eta \cdot x} f(x)$
(c) $\hat{h}(\xi)=t^{n} \hat{f}(t \xi)$ if $h(x) \coloneqq f(t^{-1} x)$
(d) $(f * g)^{\wedge}(\xi)=\hat{f}(\xi) \hat{g}(\xi)$
(e) If $x^{\vec{\alpha}} f \in L^{1}$ for $|\vec{\alpha}| \leq k$, then $\hat{f} \in C^{k}$ and $\partial_{\vec{\alpha}} \hat{f}(\xi)=[(-2 \pi i x)^{\vec{\alpha}} f(x)]^{\wedge}(\xi)$
(f) If $f \in C^{k}$, $\partial_{\vec{\alpha}} f \in L^{1}$ for $|\vec{\alpha}| \leq k$, and $\partial_{\vec{\alpha}} f \in C_{0}$ for $|\vec{\alpha}| \leq k-1$, then $(\partial_{\vec{\alpha}} f)^{\wedge}(\xi)=(2 \pi i \xi)^{\vec{\alpha}} \hat{f}(\xi)$
(g) $\overline{\hat{f}}(\xi)=(\bar{f})^{\vee}(\xi)$ and $\overline{(f^{\vee})}(\xi)=(\bar{f})^{\wedge}(\xi)$.

## Depends on

- [Definition 1.0.1 (Fourier Transform)](069-fourier-transform.md)
- [Definition 1.0.2 (Inverse Fourier transform)](070-inverse-fourier-transform.md)
- [Definition 1.0.3](071-definition-1-0-3.md)
- [Definition 2.0.6 (Translation of a function)](075-translation-of-a-function.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #16, Section 2](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
