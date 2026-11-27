# Complete convergence theorem for two-dimensional voter model perturbations

**Setting.** Let $\mathcal N\subset\mathbb Z^d$ be a finite symmetric neighbourhood of $0$ ($0\notin\mathcal N$) generating $\mathbb Z^d$, with $\sum_{z\in\mathcal N}z_iz_j/|\mathcal N|=\delta_{ij}\sigma^2$. For $\xi\in\{0,1\}^{\mathbb Z^d}$ let $f_j(x,\xi)=|\mathcal N|^{-1}\#\{y\in\mathcal N:\xi(x+y)=j\}$ and $\hat\xi=1-\xi$. The voter model has flip rates $c^{VM}(x,\xi)=\hat\xi(x)f_1(x,\xi)+\xi(x)f_0(x,\xi)$. A *finite range voter model perturbation* is a family of translation-invariant spin-flip systems $\xi^{[\varepsilon]}$, $0<\varepsilon\le\varepsilon_0$, with rates

$$c_\varepsilon(x,\xi)=c^{VM}(x,\xi)+\varepsilon\big(\hat\xi(x)g^\varepsilon_1(\xi|_{x+\mathcal N})+\xi(x)g^\varepsilon_0(\xi|_{x+\mathcal N})\big)\ge0,$$

where $g^\varepsilon_i\to g_i$ uniformly and both all-$0$ and (in $d=2$) all-$1$ are traps. Examples are the $q$-voter model $c^{(q)}=\hat\xi f_1^q+\xi f_0^q$ with $q=1-\varepsilon$, and the Neuhauser–Pacala spatial Lotka–Volterra competition model

$$c^{LV}(x,\xi)=c^{VM}(x,\xi)+\hat\xi(x)(\alpha_0-1)f_1(x,\xi)^2+\xi(x)(\alpha_1-1)f_0(x,\xi)^2$$

with interspecific competition parameters $\alpha_i=1-\varepsilon+O(\varepsilon/\log^2(1/\varepsilon))$. With $r^s(A)=g_1(1_A)$ for $A\subset\mathcal N$, the two-dimensional drift parameter is

$$\Theta_3=\sum_{\emptyset\ne A\subset\mathcal N}r^s(A)\big(\Theta^+(A)-\Theta^-(A)\big),$$

where $\Theta^\pm(A)$ are explicit constants built from the $(\log t)^{-\binom n2}$ asymptotics of non-coalescence probabilities of two-dimensional coalescing random walks started from $A$, $\mathcal N\setminus A$ and $0$.

**Theorem (complete convergence with coexistence).** Suppose $d=2$ and $\xi^{[\varepsilon]}$ is cancellative, monotone and a finite range voter model perturbation with $\Theta_3>0$. Then there is $\varepsilon_1>0$ such that for $0<\varepsilon<\varepsilon_1$ there is a translation-invariant stationary law $\nu$ with infinitely many sites of each type, and for every initial configuration $\xi_0$,

$$\xi_t\Rightarrow\beta_0(\xi_0)\,\delta_{\mathbf 0}+\beta_\infty(\xi_0)\,\nu+\beta_1(\xi_0)\,\delta_{\mathbf 1}\qquad(t\to\infty),$$

with $\beta_\infty(\xi_0)>0$ unless $\xi_0\in\{\mathbf 0,\mathbf 1\}$. In particular $\{\delta_{\mathbf 0},\nu,\delta_{\mathbf 1}\}$ are the only extremal invariant laws. For the $q$-voter model with $|\mathcal N|\le8$ in $d=2,3,4$ this holds for all $q\in(q_c,1)$ with some $q_c<1$, and $\nu=\nu_{1/2}$ is symmetric with density $1/2$.

## Expansion

In two dimensions the unperturbed voter model clusters: coalescing random walk duality makes any two sites eventually agree, so the only limits are mixtures of $\delta_{\mathbf 0}$ and $\delta_{\mathbf 1}$, and $\Theta_3=0$. Under the rescaling $x\mapsto x\sqrt N$, $t\mapsto Nt$, $\varepsilon_N\approx(\log N)^3/N$, the density of $1$'s in a perturbation converges to super-Brownian motion with drift $\Theta_2+\Theta_3$, where the drift collects the slowly decaying ($\propto1/\log t$) probabilities that neighbouring walkers have not coalesced. A positive drift means a sparse colony of one type grows, which, combined with a block comparison to supercritical oriented percolation and the cancellative (annihilating) dual, yields survival from a single site and the complete convergence theorem. For spatial Lotka–Volterra competition this gives coexistence of two species whose interspecific competition is slightly weaker than intraspecific competition, in the critical dimension where the voter model itself would cluster.

## Sources

- Ted Cox and Ed Perkins, "A complete convergence theorem for the q-voter model and other voter model perturbations in two dimensions", Electronic Journal of Probability 30 (2025), 1–86, <https://doi.org/10.1214/25-ejp1267>; numbering as in arXiv:2310.00812: Theorem 1.1, Corollary 1.2, Definition 1.8, Theorem 1.9, Theorem 1.11 and the Lotka–Volterra example of Section 3.
