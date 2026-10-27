---
article_id: af_0971b47f832569808c276772
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: TransportBurgers.l2_norm_conservation_burgers
---

# Proposition 2.0.1 (Burger's equation is a conservation law)

Let $T \geq 0$, and let $u(t,x)$ be a $C^{1}$ solution to on $S_{T} \coloneqq [0,T] \times \mathbb{R}$. Assume that for each fixed $t \in [0,T]$, we have that $\lim_{x \rightarrow \pm \infty} u(t,x)=0$. Then for $(t,x) \in S_{T}$, we have that $\int_{\mathbb{R}} u^{2}(t,x)\, dx = \int_{\mathbb{R}} u^{2}(0,x)\, dx$, i.e., the spatial $L^{2}$ norm of $u(t,\cdot)$ is preserved in time.

## Depends on

- [Definition 7.1.2 ($L^{p}$ norms)](../../part-01/class-meeting-1/008-l-p-norms.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #24, Section 2 (Burger's Equation)](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
