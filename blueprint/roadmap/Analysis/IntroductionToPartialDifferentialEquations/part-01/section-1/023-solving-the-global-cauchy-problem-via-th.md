---
article_id: af_be699cee5cf09e529838e7c8
declaration: theorem
origin: cited
statement: formalized
lean: HeatFundamental.theorem_1_1_cauchy_problem
---

# Theorem 1.1 (Solving the global Cauchy problem via the fundamental solution)

Assume that $g(x)$ is a continuous function on $\mathbb{R}^{n}$ that verifies the bounds $|g(x)| \leq a e^{b|x|^{2}}$, where $a, b>0$ are constants. Then there exists a solution $u(t, x)$ to the homogeneous heat equation $u_{t}-D \Delta u=0$, $(t>0, x \in \mathbb{R}^{n})$, $u(0, x)=g(x)$, $x \in \mathbb{R}^{n}$, existing for $(t, x) \in [0, T) \times \mathbb{R}^{n}$, where $T \coloneqq \frac{1}{4 D b}$. Furthermore, $u(t, x)$ can be represented as $u(t, x)=[g(\cdot) * \Gamma_{D}(t, \cdot)](x) = \int_{\mathbb{R}^{n}} g(y) \Gamma_{D}(t, x-y) d^{n} y = \frac{1}{(4 \pi D t)^{n/2}} \int_{\mathbb{R}^{n}} g(y) e^{-\frac{|x-y|^{2}}{4 D t}} d^{n} y$. The solution $u(t, x)$ is of regularity $C^{\infty}\left((0, \frac{1}{4 D b}) \times \mathbb{R}^{n}\right)$ (i.e., it is infinitely differentiable). Finally, for each compact subinterval $[0, T'] \subset [0, T)$, there exist constants $A, B>0$ (depending on the compact subinterval) such that $|u(t, x)| \leq A e^{B|x|^{2}}$ for all $(t, x) \in [0, T'] \times \mathbb{R}^{n}$. The solution $u(t, x)$ is the unique solution in the class of functions verifying a bound of the form $|u(t,x)| \leq A e^{B|x|^2}$.

## Depends on

- [Definition 1.0.1 (Class Meeting #5, Section 1 (The Fundamental solution))](../class-meeting-5/013-definition-1-0-1.md)
- [Definition 1.1.1](021-definition-1-1-1.md)

## Proof depends on

- [Lemma 1.0.1 (Class Meeting #5, Section 1 (The Fundamental solution))](../class-meeting-5/016-lemma-1-0-1.md)
- [Proposition 1.0.4 (Properties of $\Gamma_{D}(t, x)$)](020-t-x.md)
- [Proposition 1.1.1 (Differentiating under the integral)](022-differentiating-under-the-integral.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Section 1.1](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
