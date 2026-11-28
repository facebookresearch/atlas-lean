# Threshold stability of the infection-free state in an age-structured recidivism model

**Model.** Let $s(t,a)$, $i(t,a)$, $r(t,a)$ be the proportions of individuals of age $a$ at time $t$ who are susceptible, infectious and temporarily recovered, with $s+i+r=1$. Susceptibles are infected at rate $\beta(a)B(t)$. Infectious individuals leave through treatment or recovery at rate $\phi(a)+\gamma(a)$. Temporarily recovered individuals relapse (*recidivism*) at the nonlinear, contact-driven rate $\rho(a)B(t)$. The coefficients $\beta,\mu,\phi,\gamma,\rho$ are continuous and nonnegative, and $\mu(a)$ is the exit rate. Under proportional mixing with activity $c(a)$ and stationary demography $\mathcal F(a) = e^{-\int_0^a\mu(h)\,dh}$, the mixing density is $p_\infty(a) = c(a)\mathcal F(a)/\int_0^\infty c\,\mathcal F$, the force of infection is $B(t) = \int_0^\infty i(t,a)p_\infty(a)\,da$, and

$$
\begin{aligned}
(\partial_t + \partial_a)\, s &= -\beta(a)\, s\, B(t), \\
(\partial_t + \partial_a)\, i &= \beta(a)\, s\, B(t) - \bigl(\phi(a)+\gamma(a)\bigr) i + \rho(a)\, r\, B(t), \\
(\partial_t + \partial_a)\, r &= \bigl(\phi(a)+\gamma(a)\bigr) i - \rho(a)\, r\, B(t),
\end{aligned}
$$

with $s(t,0)=1$, $i(t,0)=r(t,0)=0$. The infection-free distribution is $s^*\equiv 1$, $i^*\equiv r^*\equiv 0$.

**Reproduction numbers.** Linearising about it gives the Euler–Lotka characteristic equation

$$
G(\lambda) := \int_0^\infty\!\!\int_0^a p_\infty(a)\,\beta(h)\, e^{-\lambda(a-h) - \int_h^a(\phi(k)+\gamma(k))\,dk}\, dh\, da = 1 ,
$$

and one defines

$$
\mathcal R_0 := G(0) = \int_0^\infty\!\!\int_0^a p_\infty(a)\,\beta(h)\,e^{-\int_h^a(\phi(k)+\gamma(k))\,dk}\,dh\,da, \qquad
\mathcal R_C := \int_0^\infty\!\!\int_0^a p_\infty(a)\,\beta(h)\,dh\,da .
$$

**Theorem.**

1. If $\mathcal R_0<1$, the infection-free distribution is locally asymptotically stable. If $\mathcal R_0>1$, it is unstable.
2. If $\mathcal R_C<1$, the infection-free distribution is globally asymptotically stable: $i(t,a)\to 0$, $r(t,a)\to 0$ and $s(t,a)\to 1$.

Since $\mathcal R_C\ge\mathcal R_0$, the gap $\mathcal R_0<1\le\mathcal R_C$ is exactly where relapse from the recovered class can sustain infection despite a subcritical $\mathcal R_0$.

## Expansion

$G$ is continuous, strictly decreasing and convex, with $G(\lambda)\to\infty$ as $\lambda\to-\infty$ and $G(\lambda)\to 0$ as $\lambda\to\infty$. So it has exactly one real root, which is dominant, and that root is negative iff $G(0)=\mathcal R_0<1$. For global stability, set $q = i + r$. Then $(\partial_t+\partial_a)q = \beta s B$, and along characteristics $q(t,a)\le\int_0^a\beta(h)B(h+t-a)s(h+t-a,h)\,dh$. Taking $C = \int_0^\infty p_\infty(a)\limsup_{t\to\infty} i(t,a)\,da$, this gives $C\le\int_0^\infty\bigl(1 - e^{-C\int_0^a\beta}\bigr)p_\infty(a)\,da$. If $C>0$, then $1\le F(C)$ with $F$ strictly decreasing and $F(0^+) = \mathcal R_C<1$, a contradiction. Hence $C=0$. The relapse term is the only route back to $i$ that does not pass through $s$, and $\mathcal R_C$ (which ignores removal from $i$) bounds it.

## Sources

- Fabio Sanchez, Juan G. Calvo, Esteban Segura, Zhilan Feng, "A partial differential equation model with age-structure and nonlinear recidivism: Conditions for a backward bifurcation and a general numerical implementation", Computers & Mathematics with Applications 78 (2019), 3916–3930, <https://doi.org/10.1016/j.camwa.2019.06.021>. Published version of arXiv:1712.09105, cited next; locators there refer to the arXiv version.
- Fabio Sanchez, Juan G. Calvo, Esteban Segura, Zhilan Feng, "A Partial Differential Equation Model with Age-Structure and Nonlinear Recidivism: Conditions for a Backward Bifurcation and a General Numerical Implementation", arXiv 2017: Section 2 (model), Section 3, Theorem 3.1, Theorem 3.2. <https://doi.org/10.48550/arXiv.1712.09105>
