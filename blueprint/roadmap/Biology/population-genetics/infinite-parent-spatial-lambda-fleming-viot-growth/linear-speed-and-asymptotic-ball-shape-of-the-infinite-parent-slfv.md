# Linear speed and asymptotic ball shape of the infinite-parent SLFV

**Model.** Let $\mu$ be a finite measure on $(0,\infty)$ with bounded support, $R_0=\inf\{r>0:\mu(r,\infty)=0\}<\infty$, and let $\Pi$ be a Poisson point process on $\mathbb R\times\mathbb R^2\times(0,\infty)$ with intensity $dt\otimes dz\otimes\mu(dr)$; a point $(t,z,r)$ is a reproduction event at time $t$ filling the closed ball $\mathcal B(z,r)$. The *$\infty$-parent spatial Lambda-Fleming-Viot process* $(S^E_t)_{t\ge0}$ started from a measurable occupied region $E\subset\mathbb R^2$ grows by adding the ball of every event that intersects the current occupied set (formally, $z\in S^E_t$ iff the backward "ancestral skeleton" from $(t,z)$, which absorbs every earlier event ball it meets, intersects $E$ at time $0$). For $A\subset\mathbb R^2$ let $\tau^E(A)=\inf\{t\ge0:A\cap S^E_t\ne\emptyset\}$, and let $\mathcal H^x=\{(x',y):x'\ge x\}$, $\mathcal H=\{(x',y):x'\le0\}$.

**Theorem (linear growth).** There is a constant $\nu\in(0,\infty)$, depending on $\mu$, such that
- $\tau^{\{0\}}(\mathcal H^x)/x\to\nu$ as $x\to\infty$, almost surely and in $L^1$;
- for every unit vector $z$, $\tau^{\{0\}}(uz)/u\to\nu$ as $u\to\infty$, almost surely and in $L^1$;
- for every $y\in\mathbb R$, $\tau^{\mathcal H}((x,y))/x\to\nu$ in probability and in $L^1$.

**Theorem (shape).** If $E$ is compact, then for every $\varepsilon>0$, almost surely

$$\mathcal B\big(0,(\nu^{-1}-\varepsilon)t\big)\subseteq S^E_t\subseteq\mathcal B\big(0,(\nu^{-1}+\varepsilon)t\big)\quad\text{for all large }t.$$

Moreover the bulk lags the tip by at most $O(\sqrt x)$: if $\sigma^E(z)$ is the first time the segment $\{uz:u\in[0,1]\}$ is entirely occupied, then for each $\varepsilon>0$ there are $\beta_\varepsilon,x_\varepsilon$ with $\mathbb P\big(\sigma^{\mathcal H}((x,0))>\tau^{\mathcal H}((x,0))+\beta\sqrt x\big)<\varepsilon$ for $\beta>\beta_\varepsilon$, $x>x_\varepsilon$.

## Depends on

- [Diffusive transverse fluctuations of infinite-parent SLFV geodesics](diffusive-transverse-fluctuations-of-infinite-parent-slfv-geodesics.md)

## Expansion

By the strong self-duality of the construction, $z\in S^{\{0\}}_t$ exactly when there is a forward *chain of reproduction events* from the origin, each event ball meeting the previous one, whose last ball contains $z$; so hitting times are first-passage times over chains. Hitting times of half-planes are subadditive under concatenation of chains, giving the limit $\nu$ by Kingman's subadditive ergodic theorem, and the Poisson process is rotation invariant, so the limit is the same in every direction and the asymptotic shape is a Euclidean ball rather than a general convex body. Exponential tail bounds $\mathbb P(\tau^{\{0\}}(z)>\beta\|z\|)\le e^{-c\beta\|z\|}$ from a slow covering strategy upgrade directional limits to the uniform shape theorem. The model was introduced to describe genetic diversity at the front of expanding populations such as bacterial colonies, where the standard SLFV (which assumes an equilibrium population of infinite density everywhere) does not apply.

## Sources

- A. Louvet, M. I. Roberts, "Asymptotics for the growth of the infinite-parent Spatial Lambda-Fleming-Viot model", arXiv:2402.00601 (2024), Definitions 1–2, Theorems 5, 6 and 7, Proposition 8, <https://doi.org/10.48550/arXiv.2402.00601>.
