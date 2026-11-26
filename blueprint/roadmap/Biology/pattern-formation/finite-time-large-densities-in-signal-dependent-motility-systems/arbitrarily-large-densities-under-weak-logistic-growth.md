# Arbitrarily large densities under weak logistic growth in signal-dependent motility systems

**Model.** On a smooth bounded domain $\Omega \subset \mathbb{R}^2$ with homogeneous Neumann boundary conditions, consider the parabolic-elliptic system with signal-suppressed motility $e^{-v}$ and a weak logistic source,

$$u_{\varepsilon t} = \Delta\big(e^{-v_\varepsilon}u_\varepsilon\big) + \varepsilon(\kappa u_\varepsilon - \mu u_\varepsilon^2), \qquad 0 = \Delta v_\varepsilon - v_\varepsilon + u_\varepsilon,$$

with $\kappa, \mu > 0$, $\varepsilon \in (0,1)$, and initial cell density $u_0$. For each fixed $\varepsilon > 0$ classical solutions are global and bounded. The formal limit $\varepsilon = 0$ is

$$u_t = \Delta(e^{-v}u), \qquad -\Delta v + v = u.$$

**Theorem.**
1. (Vanishing-source limit) For every null sequence $\varepsilon_j \to 0$ there is a subsequence along which $u_{\varepsilon_j} \to u$ in $C^0_{\mathrm{loc}}(\overline{\Omega}\times[0,\infty))$ and $v_{\varepsilon_j} \to v$ in $C^{2,0}_{\mathrm{loc}}(\overline{\Omega}\times[0,\infty))$, where $(u,v)$ is a classical solution of the limit system.
2. (Large densities) Let $\Omega = B_R(0)$, $\kappa \ge 0$, $\mu > 0$. For each mass $\Lambda \in (8\pi,\infty)\setminus 4\pi\mathbb{N}$ there is a radially symmetric $u_0 \in W^{1,q}(\Omega)$, $q > 2$, with $\|u_0\|_{L^1} = \Lambda$, such that for every $M > 0$ there are $T(M) > 0$ and $\tilde\varepsilon(M) \in (0,1)$ with: for every $\varepsilon \in (0,\tilde\varepsilon(M))$ there exist $t_\varepsilon \in (0,T(M))$ and $x_\varepsilon \in \Omega$ with $u_\varepsilon(x_\varepsilon,t_\varepsilon) > M$.

So, although logistic damping prevents blow-up, the cell density exceeds any prescribed level within a fixed finite time once the source is weak enough.

## Expansion

The key step is a family of $\varepsilon$-independent bounds on $u_\varepsilon$ and $v_\varepsilon$ in Lebesgue and Hölder spaces on finite time intervals, which gives compactness and the limit in item 1. The limit system with supercritical mass $\Lambda > 8\pi$ (avoiding the quantized values $4\pi\mathbb{N}$) has radial solutions that blow up in infinite time, by a known result for this parabolic-elliptic motility model. If the $u_\varepsilon$ stayed below $M$ on $[0,T(M)]$ for a sequence $\varepsilon\to 0$, the limit would stay below $M$ there too, contradicting the unboundedness of the limit solution, since $T(M)$ can be chosen after which it exceeds $M$. This transfers infinite-time aggregation of the limit model to transient large densities of the damped model.

## Sources

- Max Hegenbart, "Emergence of large densities in a chemotaxis system with signal-dependent motility", arXiv:2610.36934 (2026), Section 1, Theorems 1.1 and 1.2, <https://doi.org/10.48550/arXiv.2610.36934>.
