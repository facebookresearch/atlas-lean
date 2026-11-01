---
article_id: af_65430aa891b7716c40a1ad4a
declaration: theorem
origin: cited
lean: LaplacePoisson.poisson_theorem_1_1
---

# Theorem 1.1 (Solution to Poisson's equation in $\mathbb{R}^{n}$)

Let $f(x) \in C_{0}^{\infty}(\mathbb{R}^{n})$ (i.e., $f(x)$ is a smooth, compactly supported function on $\mathbb{R}^{n}$). Then for $n \geq 3$, the Laplace equation $\Delta u(x)=f(x)$ has a unique smooth solution $u(x)$ that tends to 0 as $|x| \rightarrow \infty$. For $n=2$, the solution is unique under the assumptions $\frac{u(x)}{|x|} \rightarrow 0$ as $|x| \rightarrow \infty$ and $|\nabla u(x)| \rightarrow 0$ as $|x| \rightarrow \infty$. Furthermore, these unique solutions can be represented as $u(x)=(\Phi * f)(x)= \frac{1}{2\pi} \int_{\mathbb{R}^{2}} \ln |y| f(x-y) d^{2} y$ for $n=2$, and $u(x)=-\frac{1}{\omega_{n}} \int_{\mathbb{R}^{n}}|y|^{n-2} f(x-y) d^{n} y$ for $n \geq 3$. Furthermore, there exist constants $C_{n}>0$ such that the following decay estimate holds for the solution as $|x| \rightarrow \infty$: $|u(x)| \leq C_{2} \ln |x|$ for $n=2$, and $|u(x)| \leq \frac{C_{n}}{|x|^{n-2}}$ for $n \geq 3$.

## Depends on

- [Definition 1.1.1](../section-1/021-definition-1-1-1.md)

## Proof depends on

- [Definition 1.0.1 (Class Meeting #7, Section 1 (The Fundamental Solution for $\Delta$ in $\mathbb{R}^{n}$))](032-definition-1-0-1.md)
- [Lemma 1.0.1 (Class Meeting #7, Section 1 (The Fundamental Solution for $\Delta$ in $\mathbb{R}^{n}$))](033-lemma-1-0-1.md)
- [Corollary 4.0.4 (Liouville's theorem)](../section-4/042-liouville-s-theorem.md)
- [Proposition 1.1.1 (Differentiating under the integral)](../section-1/022-differentiating-under-the-integral.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #7, Section 1 (The Fundamental Solution for $\Delta$ in $\mathbb{R}^{n}$)](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
