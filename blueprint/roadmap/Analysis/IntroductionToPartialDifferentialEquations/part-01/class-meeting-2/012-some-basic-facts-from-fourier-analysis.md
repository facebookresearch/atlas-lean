---
article_id: af_e331733c94615622d8691b31
declaration: theorem
origin: cited
statement: formalized
lean: HeatEquation.fourier_sine_theorem
---

# Theorem 4.1 (Some basic facts from Fourier analysis)

If $f(x)$ is a function such that $\|f\|_{L^{2}([0,1])}^{2} \coloneqq \int_{0}^{1}|f(x)|^{2} d x\lt \infty$, then $f(x)$ can be Fourier-expanded as $f(x)=\sum_{m=1}^{\infty} A_{m} \sin (m \pi x)$, where $A_{m}=2 \int_{[0,1]} f(x) \sin (m \pi x) d x$. The infinite sum converges in the sense that $\left\|f-\sum_{m=1}^{N} A_{m} \sin (m \pi x)\right\|_{L^{2}([0,1])} \rightarrow 0$ as $N \rightarrow \infty$. We also have the Parseval identity $\|f\|_{L^{2}([0,1])}^{2}=\sum_{m=1}^{\infty} A_{m}^{2}\|\sin (m \pi x)\|_{L^{2}([0,1])}^{2}=\sum_{m=1}^{\infty} \frac{1}{2} A_{m}^{2}$. Furthermore, if $f$ is continuous on $[0,1]$, then for any subinterval $[a, b] \subset(0,1)$, $\left\|f-\sum_{m=1}^{N} A_{m} \sin (m \pi x)\right\|_{C^{0}([a, b])} \rightarrow 0$ as $N \rightarrow \infty$, i.e., the convergence is uniform on any closed subinterval $[a, b]$ of the open interval $(0,1)$.

## Depends on

- [Definition 7.1.1 ($C^{k}$ norms)](../class-meeting-1/007-c-k-norms.md)
- [Definition 7.1.2 ($L^{p}$ norms)](../class-meeting-1/008-l-p-norms.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #2, Section 4 (Separation of variables)](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
