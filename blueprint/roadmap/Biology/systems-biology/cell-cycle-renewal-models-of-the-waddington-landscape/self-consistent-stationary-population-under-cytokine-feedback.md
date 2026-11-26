# Self-consistent stationary population of a kinetotype-structured cell-cycle model under cytokine feedback

**Model.** Let $\Omega\subset\mathbb R^m$ be a bounded domain of epigenetic states and $Q(\mathbf x,t)$ the density of quiescent, proliferatively competent cells. A cell in state $\mathbf x$ re-enters the cycle at rate $\beta(c,\mathbf x)$, which depends on a global cytokine signal $c(t)=\int_\Omega\xi(\mathbf x)Q(\mathbf x,t)\,d\mathbf x$, exits irreversibly (differentiation, senescence) at rate $\kappa(\mathbf x)$, and, after a cycle of duration $\tau(\mathbf y)$ with survival probability $\sigma(\mathbf y)=e^{-\mu(\mathbf y)\tau(\mathbf y)}$, produces two daughters whose states are redistributed by an inheritance kernel $p(\mathbf x,\mathbf y)\ge0$ with $\int_\Omega p(\mathbf x,\mathbf y)\,d\mathbf x=1$:
$$\partial_tQ(\mathbf x,t)=-\big(\beta(c(t),\mathbf x)+\kappa(\mathbf x)\big)Q(\mathbf x,t)+2\int_\Omega\beta\big(c(t-\tau(\mathbf y)),\mathbf y\big)\,Q\big(\mathbf y,t-\tau(\mathbf y)\big)\,\sigma(\mathbf y)\,p(\mathbf x,\mathbf y)\,d\mathbf y.$$
The renewal equation is posed with a nonnegative history on $[-\tau_{\max},0]$ and is coupled to a Fokker–Planck equation with division-driven redistribution for the normalized epigenetic density $f$.

**Well-posedness.** Under bounded, measurable, state-dependent delays and rates, the renewal equation has, for every $T>0$, a unique mild solution $Q\in C([-\tau_{\max},T];L^1(\Omega))$, nonnegative for nonnegative history and depending continuously on it; the coupled epigenetic density equation has a unique global mild solution that stays in the probability simplex.

**Stationary states.** For fixed $c$ define the next-generation operator $(\mathcal T_cQ)(\mathbf x)=\int_\Omega K_c(\mathbf x,\mathbf y)Q(\mathbf y)\,d\mathbf y$ with
$$K_c(\mathbf x,\mathbf y)=\frac{2\beta(c,\mathbf y)\,\sigma(\mathbf y)\,p(\mathbf x,\mathbf y)}{\beta(c,\mathbf x)+\kappa(\mathbf x)}.$$

**Theorem.** Suppose $K_c$ is continuous, bounded and a.e. positive for $c\in[c_0,c_1]$, $c\mapsto\rho(\mathcal T_c)$ is continuous, and $\rho(\mathcal T_{c_0})>1>\rho(\mathcal T_{c_1})$. Then there is $c^*\in(c_0,c_1)$ with $\rho(\mathcal T_{c^*})=1$ and a stationary density $Q^*\in L^1(\Omega)$, strictly positive a.e., with $\mathcal T_{c^*}Q^*=Q^*$ and $c^*=\int_\Omega\xi Q^*$; the shape of $Q^*$ is unique. With the reproduction factor
$$G_c(\mathbf y)=2\beta(c,\mathbf y)\,\sigma(\mathbf y)\int_\Omega\frac{p(\mathbf x,\mathbf y)}{\beta(c,\mathbf x)+\kappa(\mathbf x)}\,d\mathbf x,$$
one has $\operatorname{ess\,inf}G_c\le\rho(\mathcal T_c)\le\operatorname{ess\,sup}G_c$, so $\operatorname{ess\,inf}G_{c_0}>1$ and $\operatorname{ess\,sup}G_{c_1}<1$ suffice for the crossing; $\rho(\mathcal T_c)$ is continuous in $c$ when $\beta+\kappa$ is bounded above and below.

## Expansion

At a stationary state the delayed influx equals the outflux, which after dividing by $\beta+\kappa$ is the fixed-point equation $Q=\mathcal T_cQ$. $\mathcal T_c$ is compact (continuous kernel on a bounded domain) and positivity improving, so by Krein–Rutman/Jentzsch its spectral radius is a simple eigenvalue with an a.e. positive eigenfunction, unique up to scaling. The intermediate value theorem gives $c^*$ with $\rho=1$; scaling the eigenfunction to match $\int\xi Q^*=c^*$ closes the cytokine loop. The bounds by $G_c$ follow by integrating $\mathcal T_c\varphi$ against the normalized kernel, which is a column-sum (Collatz–Wielandt) estimate in $L^1$.

## Sources

- Yuling Xue, Jinzhi Lei, "A unified cross-scale framework for the dynamic Waddington landscape", arXiv:2611.19257 (2026), Section 2 (population renewal model) and Section 3 (Theorems 1, 3 and 5, Proposition 4, Theorem 7, Propositions 8–9), <https://doi.org/10.48550/arXiv.2611.19257>.
