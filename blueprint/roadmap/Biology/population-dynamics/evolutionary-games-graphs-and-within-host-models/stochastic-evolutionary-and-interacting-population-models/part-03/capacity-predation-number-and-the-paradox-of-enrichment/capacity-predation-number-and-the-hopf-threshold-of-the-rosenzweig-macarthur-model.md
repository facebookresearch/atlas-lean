# Capacity–predation number and the Hopf threshold of the Rosenzweig–MacArthur model

**Model.** For prey $U$ and predator $V$,

$$
\frac{dU}{dT} = \alpha U\Big(1-\frac{U}{b}\Big) - \gamma\frac{U}{U+h}V,\qquad
\frac{dV}{dT} = \Big(\kappa\gamma\frac{U}{U+h} - \mu\Big)V,
$$

with prey growth rate $\alpha$, carrying capacity $b$, half-saturation $h$, predation intensity $\gamma$, conversion efficiency $\kappa$ and predator mortality $\mu$, all positive. With $u=U/b$, $v=V\gamma/(\alpha b)$, $t=\alpha T$ it becomes

$$
\frac{du}{dt} = u(1-u) - \frac{u}{u+H}v,\qquad \frac{dv}{dt} = k\Big(\frac{u}{u+H}-r\Big)v,
$$

with the **capacity–predation number** $H=h/b$, the mortality–food number $r=\mu/(\kappa\gamma)$ and $k=\kappa\gamma/\alpha$.

**Theorem.** Let $0<r<1$.

1. $(0,0)$ is a saddle. $(1,0)$ is a stable node if $H>\frac1r-1$ and a saddle if $0<H<\frac1r-1$; in the latter case there is a unique coexistence equilibrium

$$
u_* = \frac{r}{1-r}H,\qquad v_* = (1-u_*)(u_*+H).
$$

2. The linearization at $(u_*,v_*)$ has eigenvalues $\lambda=r\Big[\tfrac12(1-2u_*-H)\pm\sqrt{\tfrac14(1-2u_*-H)^2-kH\frac{1-u_*}{u_*}}\Big]$, so the coexistence equilibrium is locally asymptotically stable for $\frac{1-r}{1+r}<H<\frac{1-r}{r}$ and unstable for $0<H<\frac{1-r}{1+r}$, with a Hopf bifurcation at $H=\frac{1-r}{1+r}$ (equivalently, $u_*$ crosses the vertex $\tfrac12(1-H)$ of the prey-nullcline parabola). This corrects (4.4) of arXiv:1104.4355, which prints these eigenvalues without the factor $r$; the factor follows from the displayed linearization, since $u_*/(u_*+H)=r$.
3. For $0<H<\frac{2}{1+r}-1$, the $\omega$-limit set of every point of the open quadrant other than $(u_*,v_*)$ is a periodic orbit; if all these limit sets are one stable limit cycle, it encircles $(u_*,v_*)$.

**Paradox of enrichment, recast.** Increasing $b$ with the other parameters fixed decreases $H$ and eventually destabilizes coexistence, producing a limit cycle that approaches the $v$-axis, so prey densities get dangerously small. Since $H=h/b$, the same effect is produced by decreasing the half-saturation $h$, i.e. by more aggressive predation, for which instability is unsurprising.

## Expansion

The prey nullcline is the parabola $v=(1-u)(u+H)$ with vertex at $u=\tfrac12(1-H)$, and the predator nullcline is the vertical line $u=u_*$. The real part of the eigenvalues at the crossing has the sign of $1-2u_*-H$, the slope of the parabola there: the equilibrium is stable on the descending branch and unstable on the ascending branch (Rosenzweig's graphical criterion). Solving $u_*=\tfrac12(1-H)$ with $u_*=rH/(1-r)$ gives $H=\frac{1-r}{1+r}$. Below this value the equilibrium is a repeller and solutions are bounded, so Poincaré–Bendixson forces periodic $\omega$-limit sets. Expressed in $H$, enrichment and predation efficiency are a single control parameter.

## Sources

- Z. C. Feng, Y. C. Li, *A resolution of the paradox of enrichment*, arXiv:1104.4355 (2011). <https://doi.org/10.48550/arXiv.1104.4355> — Sections 2–4 (dimensionless model and stability analysis), Theorems 6.1 and 6.3 (periodic $\omega$-limit sets and the limit cycle). Published version: International Journal of Bifurcation and Chaos 25(06) (2015), article 1550094, <https://doi.org/10.1142/s0218127415500947>; locators above refer to the arXiv version.
