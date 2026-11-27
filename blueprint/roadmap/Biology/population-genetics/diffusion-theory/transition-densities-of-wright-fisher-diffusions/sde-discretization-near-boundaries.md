# Boundary-preserving discretization of the Wright–Fisher SDE

Standard Euler–Maruyama schemes fail for the Wright–Fisher diffusion: simulated paths can leave $[0, 1]$, and the usual weak and strong convergence results assume a Lipschitz diffusion coefficient (Jenkins and Spanò 2017, Section 1). Neuenkirch and Szpruch (Section 3.5) treat

$$dy(t) = (a - by(t))\,dt + \gamma\sqrt{|y(t)(1 - y(t))|}\,dw(t), \qquad y_0 \in (0, 1),$$

with $a, b, \gamma > 0$, $2a/\gamma^2 \ge 1$ and $2(b - a)/\gamma^2 \ge 1$, under which it has a unique strong solution that stays in $(0, 1)$; after the time change $s = \gamma^2t$ the equation is the [Wright–Fisher equation](../wright-fisher-diffusion-with-mutation/unique-strong-solution-of-the-wf-sde.md) with $\alpha = 0$, $\theta_1 = 2a/\gamma^2$ and $\theta_2 = 2(b - a)/\gamma^2$, which has a unique strong solution, and the non-attainment of the boundary under the two conditions is from Neuenkirch and Szpruch. The Lamperti transformation $x = 2\arcsin\sqrt y$ gives $dx(t) = f(x(t))\,dt + \gamma\,dw(t)$ on $(0, \pi)$ with $f(x) = (a - \gamma^2/4)\cot(x/2) - (b - a - \gamma^2/4)\tan(x/2)$; this equation is discretized by the drift-implicit (backward) Euler–Maruyama scheme $X_k$ with step $\Delta t$, and $y$ is approximated by $\sin^2(X_k/2)$, which lies in $[0, 1]$. For $2 \le p < \frac{4}{3\gamma^2}\min\{a, b - a\}$ the scheme is $p$-strongly convergent with order one,

$$E\Bigl[\sup_{k=0,\dots,\lceil T/\Delta t\rceil}\Bigl|y(t_k) - \sin^2\Bigl(\frac{X_k}{2}\Bigr)\Bigr|^p\Bigr] \le C_p\,\Delta t^p$$

(Proposition 3.4, from their general Theorem 2.7).

## Depends on

- [The coefficient √(x(1 − x)) is 1/2-Hölder on the unit interval](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/abs-sqrt-mul-one-sub-sub-le.md)
- [Exact simulation of the Wright–Fisher diffusion](../../../../Biology/population-genetics/diffusion-theory/transition-densities-of-wright-fisher-diffusions/exact-simulation-of-the-wright-fisher-diffusion.md)
- [Unique strong solution of the Wright–Fisher stochastic differential equation](../wright-fisher-diffusion-with-mutation/unique-strong-solution-of-the-wf-sde.md)

## Expansion

1. The equation and its unique strong solution in $(0, 1)$ under the two parameter conditions.
2. The Lamperti transformation and the one-sided Lipschitz property of the transformed drift.
3. The drift-implicit Euler scheme for the transformed equation, its solvability on $(0, \pi)$, and the inverse transformation.
4. Inverse-moment bounds for $y$ and $1 - y$ and the strong order-one error bound for $2 \le p < 4\min\{a, b - a\}/(3\gamma^2)$.
5. An explicit example in which the explicit Euler–Maruyama scheme leaves $[0, 1]$ with positive probability.

## Sources

- A. Neuenkirch and L. Szpruch, First order strong approximations of scalar SDEs defined in a domain, Numer. Math. 128 (2014), 103–136, Section 3.5, Proposition 3.4 and Theorem 2.7. <https://doi.org/10.1007/s00211-014-0606-4> <https://arxiv.org/abs/1209.0390>
- P. A. Jenkins and D. Spanò, Exact simulation of the Wright–Fisher diffusion, Ann. Appl. Probab. 27 (2017), 1478–1509, Section 1. <https://doi.org/10.1214/16-AAP1236>
