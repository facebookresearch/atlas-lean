# Bang-bang activity maximizers in the linearized SEIR model

**Model.** At low prevalence, with time measured in mean incubation periods and mean infectious period $1/\gamma$, the linearized SEIR dynamics are

$$\dot E(t)=-E(t)+\beta(t)I(t),\qquad \dot I(t)=E(t)-\gamma I(t),$$

where the transmission rate $\beta:[0,T]\to[\beta_{\min},\beta_{\max}]$ is a measurable control interpreted as the total amount of transmission-inducing activity. The objective is to maximize the total activity $A=\int_0^T\beta(t)\,dt$ for given $E(0),I(0),E(T),I(T)$, optionally with the prevalence constraint $C_1\le\log I(t)\le C_2$.

**Velocity reduction.** With $V=E/I$ and $\phi(x)=x^2+(1-\gamma)x$,

$$\frac{d}{dt}\log I=V-\gamma,\qquad \dot V=\beta-\phi(V),\qquad A=\int_0^TV(t)^2dt+(1-\gamma)\int_0^TV(t)dt+V(T)-V(0).$$

Fixing the four boundary values up to a common factor is the same as fixing $V(0)$, $V(T)$ and $\int_0^TV\,dt$, so the problem is equivalent to maximizing $\int_0^TV^2dt$ over Lipschitz $V$ with $\beta_{\min}-\phi(V)\le\dot V\le\beta_{\max}-\phi(V)$, i.e. to maximizing the variance of $V$ over time at fixed mean. Write $v_{\min}=\phi^{-1}(\beta_{\min})$ and $v_{\max}=\phi^{-1}(\beta_{\max})$ (positive roots); constant $\beta=b$ drives $V$ to $\phi^{-1}(b)$.

**Proposition (worst policy).** If $V(0)=V(T)\in[v_{\min},v_{\max}]$ and $\int_0^TV\,dt=TV(0)$, the activity-minimizing solution is the constant one, $V\equiv V(0)$, i.e. $\beta\equiv\phi(V(0))$.

**Proposition (best unconstrained policy).** If $V(T)>V(0)$, every optimal solution has $\beta=\beta_{\max}$ on a single interval and $\beta=\beta_{\min}$ before and after it; if $V(T)<V(0)$, $\beta=\beta_{\min}$ on a single interval and $\beta=\beta_{\max}$ before and after; if $V(T)=V(0)$ there is an optimal solution of each type.

**Proposition (best policy between prevalence walls).** Under $C_1\le\log I\le C_2$ with $\gamma\in(v_{\min},v_{\max})$, $\log I(0),\log I(T)\in\{C_1,C_2\}$ and $V(0)=V(T)=\gamma$, every optimal $\beta$ switches between $\beta_{\min}$ and $\beta_{\max}$ finitely many times. The excursions of $V$ away from $\gamma$ alternate above ($\beta_{\max}$ rising, $\beta_{\min}$ falling) and below ($\beta_{\min}$ falling, $\beta_{\max}$ rising) and all carry $\log I$ from one wall to the other, except possibly two smaller excursions of equal area. For general boundary data, between the first and last wall contacts an optimal solution behaves this way, and outside them (or if no wall is hit) it has the form of the unconstrained optimum.

## Depends on

- [Solution of the closed SEIR system for times t ≥ 0](../seir-epidemic-model/is-solution.md)

## Expansion

The reduction is a direct computation: $\dot V=(\dot EI-\dot IE)/I^2=\beta-V^2+(\gamma-1)V$, so $\beta=\dot V+\phi(V)$, and integrating gives $A$; the linear terms are fixed by the boundary data, leaving $\int V^2$. Since the mean of $V$ is fixed, a constant $V$ has zero variance and is worst. For the best policy, if $V$ is not of the stated form one can modify it on two intervals so that $\int V$ is unchanged but $\int V^2$ increases, pushing $V$ toward the extremes $v_{\min},v_{\max}$ as fast as the bounds on $\dot V$ allow. A mechanical picture: $X=\log I+\gamma t$ is the position of a car, $V$ its velocity, $\beta$ the throttle and $-\phi(V)$ quadratic drag; maximizing activity is wasting fuel, best done by alternately flooring and releasing the pedal between two trucks (the prevalence walls). In the source's example with $\gamma=1$, $\beta\in[1/4,9/4]$ and $I$ oscillating by a factor of about $13.5$, alternation allows about 20% more activity than the constant policy $\beta\equiv1$. For several weakly coupled subpopulations, total activity equals a constant plus $\sum_k\int V_k^2-\sum_{j\ne k}\int\alpha_{jk}\cosh(X_j-X_k)$ when couplings are symmetric, so activity is largest under policies that are oscillatory but coordinated across subpopulations.

## Sources

- S. Sheffield, "Best and worst policy control in low-prevalence SEIR", arXiv:2009.07792 (2020), Section 2 (linearized model, Problems 2.1–2.3, velocity reduction), Section 3 (Propositions 3.1, 3.2, 3.3 and the multiple-subpopulation identity) and the appendix (proofs and general utilities), <https://doi.org/10.48550/arXiv.2009.07792>.
