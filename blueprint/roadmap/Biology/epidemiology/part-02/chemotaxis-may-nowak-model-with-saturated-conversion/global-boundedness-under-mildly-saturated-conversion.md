# Global boundedness of the chemotaxis May–Nowak model under mildly saturated conversion

Let $\Omega \subset \mathbb R^n$ be a smooth bounded domain. Uninfected cells $u$, infected cells $v$ and virus particles $w$ obey the chemotaxis May–Nowak system

$$u_t = \Delta u - \nabla\cdot(u\nabla v) - u - f(u)\,w + \kappa, \qquad v_t = \Delta v - v + f(u)\,w, \qquad w_t = \Delta w - w + v,$$

in $\Omega \times (0,\infty)$ with homogeneous Neumann boundary conditions, where $\kappa \ge 0$ is a constant source of uninfected cells, uninfected cells move up gradients of infected cells, and the infection (conversion) term $f(u)w$ uses $f \in C^1([0,\infty))$ with

$$f \ge 0, \qquad f(0) = 0, \qquad f(s) \le K_f\, s^{\alpha} \quad \text{for all } s \ge 1,$$

for some $K_f > 0$ and $\alpha \in \mathbb R$. The case $f(s) = s$ ($\alpha = 1$) is the classical mass-action infection; saturating responses such as Holling type II or Beddington–DeAngelis have $\alpha = 0$; $f(s) = s/(1 + s^{1-\alpha})$ interpolates.

**Theorem.** If

$$\alpha < \frac{2}{n},$$

then for all nonnegative $u_0 \in C^0(\overline\Omega)$, $v_0 \in W^{1,\infty}(\Omega)$, $w_0 \in C^0(\overline\Omega)$ the system has a unique nonnegative global classical solution, and it is bounded: there is $C > 0$ with

$$\|u(\cdot,t)\|_{L^\infty(\Omega)} + \|v(\cdot,t)\|_{W^{1,\infty}(\Omega)} + \|w(\cdot,t)\|_{L^\infty(\Omega)} < C \qquad \text{for all } t > 0.$$

In particular, in one dimension even super-linear conversion $f(s) = s^\alpha$ with $\alpha < 2$ cannot produce blow-up, and in every dimension a sufficiently saturated infection rate rules out chemotactic collapse without any logistic damping.

## Expansion

Total mass of $u + v$ is bounded in $L^1$ by integrating the first two equations. A semigroup bootstrap couples the virus and the infected-cell gradient: $\|w\|_{L^\infty} \lesssim 1 + \sup\|\nabla v\|_{L^q}^b$ with $b \in (0,1)$ for $q > \max\{1, n/2\}$, while $\|\nabla v\|_{L^q} \lesssim 1 + \sup\|w\|_{L^\infty}$ for $q < n/(\alpha n - 1)_+$, using only $\|f(u)\|_{L^{1/\alpha}} \lesssim \|u\|_{L^1}^{\alpha}$. When $\alpha < 2/n$ one can pick $q > n$ in both ranges, and the sublinear exponent $b$ closes the loop, giving uniform bounds on $\nabla v$ in $L^q$ ($q > n$) and on $w$ in $L^\infty$. With $\nabla v$ bounded in $L^q$, $q > n$, a Moser-type or semigroup iteration bounds $u$ in $L^\infty$, and the extensibility criterion yields global existence. In one dimension with $\alpha \in [1,2)$ an extra energy estimate on $\|v_x\|_{L^2}$ replaces the first step.

## Sources

- Mario Fuest, "Boundedness enforced by mildly saturated conversion in a chemotaxis-May-Nowak model for virus infection", arXiv (2018). Section 1 (system (P), condition on $f$, Theorem 1.1), Section 2 (Lemmas 2.1 and 2.2), Section 3 (Lemmas 3.1–3.5), Section 4 (Lemma 4.1). <https://doi.org/10.48550/arXiv.1809.10960>. Published version: Journal of Mathematical Analysis and Applications 472(2) (2019), 1729–1740, <https://doi.org/10.1016/j.jmaa.2018.12.020>; locators above refer to the arXiv version.
