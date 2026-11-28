# Chemostat with planktonic and aggregated biomass and its density-dependent reduction

**Setting.** In a chemostat with dilution rate $D$ and input substrate $S_{in}$, biomass occurs in a planktonic form $u$ and an aggregated (flocs or attached) form $v$ consuming substrate $s$ with unit yields:

$$\dot s = D(S_{in} - s) - \mu_u(s)u - \mu_v(s)v, \qquad \dot u = \mu_u(s)u - D_u u - \alpha(u,v)u + \beta(v)v, \qquad \dot v = \mu_v(s)v - D_v v + \alpha(u,v)u - \beta(v)v.$$

Assumptions: (i) $\mu_u, \mu_v$ are smooth, increasing, zero at zero, with $\mu_u(s) > \mu_v(s)$ for $s > 0$ (aggregates have less access to substrate); (ii) $D \ge D_u \ge D_v > 0$; (iii) the attachment rate $\alpha(u,v)$ is increasing, $\alpha(u,0) > 0$ for $u > 0$, and $\partial_u\alpha \ge \partial_v\alpha$; (iv) the detachment rate $\beta(v)$ is decreasing, $\beta(v) > 0$ for $v > 0$, and $v \mapsto \beta(v)v$ is increasing.

**Theorem.**
1. The nonnegative orthant is forward invariant and solutions are bounded. No steady state has only one form of biomass present.
2. (Coexistence, $D_u = D_v = D$.) With $\alpha(u,v) = a(u+v)$ and $\beta(v) = b$, $a, b > 0$, the system has a unique coexistence steady state if and only if $D < \mu_u(S_{in})$, and it is locally exponentially stable.
3. (Fast attachment and detachment.) Let $x = u + v$ and $p = u/x$, and suppose attachment and detachment are fast, $\dot p = \varepsilon^{-1} g(x,p)$. Then for every $x > 0$ there is a unique $\bar p(x) \in (0,1)$ with $g(x,\bar p(x)) = 0$; it is $C^1$, strictly decreasing, and globally asymptotically stable for the fast dynamics (for linear attachment, $\bar p(x) = 1/(1 + a x/b)$). By Tikhonov's theorem the slow dynamics are those of a chemostat with **density-dependent growth**

$$\dot s = D(S_{in} - s) - \mu(s,x)\,x, \qquad \dot x = \mu(s,x)\,x - d(x)\,x,$$

with $\mu(s,x) = \bar p(x)\mu_u(s) + (1 - \bar p(x))\mu_v(s)$, decreasing in $x$, and $d(x) = \bar p(x)D_u + (1 - \bar p(x))D_v$, which is constant equal to $D$ when removal rates are equal and decreasing in $x$ when $D_v < D_u$.

## Expansion

The fraction $\bar p(x)$ of free biomass decreases with total biomass because aggregation is driven by encounters, so a denser culture spends more of its biomass in the slower-growing aggregated form: this is a mechanistic derivation of the Contois-type growth laws $\mu(s,x)$ used empirically in wastewater treatment. Uniqueness and global stability of $\bar p$ follow from $g(x,0) = \beta > 0$, $g(x,1) = -\alpha(x,0) < 0$ and $\partial_p g < 0$; the implicit function theorem gives $\bar p' < 0$. With distinct removal rates, let $\lambda_u, \lambda_v$ be the break-even concentrations, $\mu_u(\lambda_u) = D_u$ and $\mu_v(\lambda_v) = D_v$; unlike the equal-rate case, where $\lambda_u < \lambda_v$, either order can now occur. Besides washout $(S_{in},0)$, a positive equilibrium must satisfy $s^\star = S_{in} - x^\star d(x^\star)/D$ and $\mu(s^\star,x^\star) = d(x^\star)$, which forces $s^\star \in [\min(\lambda_u,\lambda_v), \max(\lambda_u,\lambda_v)]$ and reduces existence to the zeros of a scalar function $\Gamma(x) = S_{in} - x\,d(x)/D - \phi(x)$, where $\phi(x)$ solves $\mu(\phi(x),x) = d(x)$. A density-dependent removal rate of this kind had not previously been derived for chemostat models.

## Sources

- ALAIN RAPAPORT, "Properties of the chemostat model with aggregated biomass", European Journal of Applied Mathematics 29 (2018), 972–990, <https://doi.org/10.1017/s0956792518000141>. Published version of arXiv:1803.02634, cited next; locators there refer to the arXiv version.
- Alain Rapaport, "Properties of the chemostat model with aggregated biomass", arXiv:1803.02634 (2018), Section 2 (model and Assumptions, Lemma 1), Section 3 (Propositions 3.1 and 3.2), Section 4 (fast attachments and detachments, Proposition 4.1) and Section 5 (distinct removal rates), <https://doi.org/10.48550/arXiv.1803.02634>.
