---
article_id: af_0b6b3952e5c56bfb9f38e2a2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: FourierSeries.fejer_kernel_properties
---

# Proposition (April 15, 2021)

For all $f \in L^2([-\pi, \pi])$, we have $\sigma_N f(x) = \int_{-\pi}^\pi K_N(x-t) f(t) \, dt$, where $K_N(x) = \begin{cases} \frac{N+1}{2\pi} & x = 0 \\ \frac{1}{2\pi(N+1)} \left(\frac{\sin\left(\frac{N+1}{2} x\right)}{\sin \frac{x}{2}}\right)^2 & \text{otherwise} \end{cases}$. The function $K_N(x)$ is called the Fejer kernel, and it has the following properties: (1) $K_N(x) \geq 0$ and $K_N(x) = K_N(-x)$ for all $x$, (2) $K_N$ is periodic with period $2\pi$, (3) $\int_{-\infty}^{\infty} K_N(t) \, dt = 1$, and (4) for any $\delta \in (0, \pi)$ and for all $\delta \leq |x| \leq \pi$, we have $|K_N(x)| \leq \frac{1}{2\pi(N+1) \sin^2\frac{\delta}{2}}$.

## Depends on

- [Definition ($L^p$ space)](../april-6/045-l-p-space.md)
- [Definition (April 13, 2021)](../april-13/051-definition.md)

## Sources

- [MIT 18.102 Introduction to Functional Analysis (Spring 2021), April 15, 2021](../../../../../sources/v1/IntroductionToFunctionalAnalysis.md)
