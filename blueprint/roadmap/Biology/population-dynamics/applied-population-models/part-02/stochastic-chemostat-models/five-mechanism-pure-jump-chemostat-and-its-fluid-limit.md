# Five-mechanism pure jump chemostat and its fluid limit

The deterministic chemostat with biomass $b$, substrate $s$, dilution rate $D>0$, feed concentration $s^{\rm in}$, yield coefficient $k>0$ and specific growth rate $\mu$ (non-negative, $\mu(0)=0$, $\mu(s)>0$ for $s>0$, $\mu\le\mu_{\max}<\infty$, continuous at $0$; e.g. Monod or Haldane) is

$$\dot b=[\mu(s)-D]\,b,\qquad \dot s=-k\,\mu(s)\,b+D\,(s^{\rm in}-s).$$

**Pure jump model.** Fix scale parameters $K=(K_1,\dots,K_5)$, $K_i>0$. The process $X_t=(B_t,S_t)$ on $\mathbb{R}_+^2$ jumps according to five mechanisms with rates $\lambda_i(x)$ and jumps $\nu_i(x)$, $x=(b,s)$:

| mechanism | rate $\lambda_i(x)$ | jump $\nu_i(x)$ |
|---|---|---|
| biomass growth | $K_1\mu(s)b$ | $(1/K_1,\,0)$ |
| substrate consumption | $K_2k\mu(s)b$ | $(0,\,-(1\wedge K_2s)/K_2)$ |
| substrate inflow | $K_3Ds^{\rm in}$ | $(0,\,1/K_3)$ |
| biomass outflow | $K_4Db$ | $(-(1\wedge K_4b)/K_4,\,0)$ |
| substrate outflow | $K_5Ds$ | $(0,\,-(1\wedge K_5s)/K_5)$ |

so each mechanism has the mean increment prescribed by the stochastic mass-action law, while $K_i$ sets its variance (small frequent jumps for large $K_i$). Equivalently $X_t=X_0+\sum_{i=1}^5\int_{(0,t]\times[0,\infty)}\nu_i(X_{u-})\mathbf{1}_{\{v\le\lambda_i(X_{u-})\}}N^i(du\,dv)$ with independent Poisson random measures $N^i$ of Lebesgue intensity.

**Statement.**
1. The process is non-explosive (defined for all $t\ge0$), has finite moments whenever $X_0$ does, stays in $\mathbb{R}_+^2$, and solves the jump SDE above. Away from the strip $\{b\le1/K_4\}\cup\{s\le1/K_2\}\cup\{s\le1/K_5\}$ its drift $\sum_i\lambda_i(x)\nu_i(x)$ equals the chemostat vector field.
2. *Fluid limit.* Assume in addition that $\mu$ is locally Lipschitz on $[0,\infty)$ (as Monod and Haldane kinetics are) and that $X^K_0\to x(0)$ in probability. If $x(t)$ solves the deterministic chemostat with the same initial condition, then for all $T>0$ and $\delta>0$,

$$\mathbb{P}\Big(\sup_{0\le t\le T}\|X^K_t-x(t)\|\ge\delta\Big)\to0\qquad\text{as } K_i\to\infty\ \text{for all } i .$$

## Expansion

The jumps are aggregated packets of individual events, so the process is mesoscopic: it keeps the geometry of the chemostat (positivity, the five physical fluxes) while letting the variance of each flux be tuned separately, e.g. bacterial mass is about $10^6$ times a substrate molecule's, so $K_1,K_4\ll K_2,K_3,K_5$ is typical. The fluid limit is Kurtz's law of large numbers for density-dependent jump processes: the compensated martingales have quadratic variation $O(1/K_i)$, and Gronwall's inequality on the Lipschitz drift gives uniform convergence in probability.

## Depends on

- [Chemostat equilibria and the washout threshold](../../../chemostat/chemostat-equilibria-and-washout.md)

## Proof depends on

- [Gronwall inequality in integral form](../../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Sources

- F. Campillo, M. Joannides and I. Larramendy-Valverde, *Stochastic models of the chemostat*, arXiv:1011.5108 (2010), <https://doi.org/10.48550/arXiv.1011.5108>. Section "Models at different scales": pure jump model (rate/jump table) and asymptotic analysis; appendix "Representation of the process $X_t$" (jump SDE representation and non-explosion).
