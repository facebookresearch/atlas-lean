# Growth phases of SI epidemics with degree- and distance-dependent rates

**Network.** A GIRG with parameters $\tau>2$, $\alpha>1$ and dimension $d\ge1$: vertices form a unit-intensity Poisson process on a volume-$n$ torus (or box) in $\mathbb R^d$, each vertex gets an i.i.d. weight $W_v$ with power-law tail of exponent $\tau$ (so degrees have power-law exponent $\tau$), and $u,v$ are joined independently with probability

$$p_{uv}=c\,\min\Big\{\frac{W_uW_v}{\|u-v\|^d},1\Big\}^{\alpha}.$$

**Epidemic.** An SI process starts from one vertex; across an edge $\{u,v\}$ infection passes at rate $(W_uW_v)^{-\mu}\|u-v\|^{-\zeta}$ with $\mu,\zeta\ge0$ (busy hubs and long links transmit more slowly). Let $I(t)$ be the number of vertices infected by time $t$.

**Theorem (growth phases).**

- (i) Explosive growth (infinitely many infections in finite time in the limit) if $\mu+\zeta/d<(3-\tau)/2$.
- (ii) Quasi-exponential growth $I(t)\approx\exp(t^{\varphi})$ with $\varphi\le1$ if $\mu+\zeta/d>(3-\tau)/2$ and either $\zeta/d<2-\alpha$ or $\mu+\zeta/d<3-\tau$.
- (iii) Polynomial growth $I(t)\approx t^{d\psi}$ with $\psi>1$ if $\mu+\zeta/d>3-\tau$ and $\zeta/d>2-\alpha$, and moreover one of: $\alpha<2$ and $\zeta/d<2-\alpha+1/d$; $\alpha>2$, $\tau<3$ and $\mu<(1-\zeta)\big(\frac1d+\frac{3-\tau}{d(\alpha-2)}\big)$; $\tau<3$ and $\mu+\zeta/d<3-\tau+1/d$.
- (iv) Purely geometric growth $I(t)\approx t^d$ otherwise; in particular for all $\mu,\zeta\ge0$ when $\tau>3$ and $\alpha>2$.

The exponents $\varphi,\psi$ are explicit functions of $(d,\mu,\zeta,\tau,\alpha)$, with $I(t)\lesssim\exp(t^{(1+o(1))\varphi})$ in phase (ii) and $I(t)\sim t^{d\psi(1+o(1))}$ in phases (iii)–(iv).

**Edge-length tails.** As $n\to\infty$, the number of GIRG edges longer than $L$, and the number of such edges with $W_uW_v\le M$, have explicit power-law asymptotics in $L$ with explicit constants; these tails determine when long edges speed up the epidemic.

## Depends on

- [Epidemics on networks](../epidemics-on-networks/README.md)

## Expansion

The SI arrival time at a vertex is a first-passage distance with i.i.d. exponential edge times scaled by the rates. Phase (i) is the scale-free explosion: paths through ever larger hubs have summable transmission times when the slow-down exponent $\mu+\zeta/d$ is below $(3-\tau)/2$. Above it, hubs or long edges still create shortcuts that let the infected ball grow faster than its geometric volume, giving stretched-exponential or polynomial growth; when both the degree tail is light ($\tau>3$) and long edges are rare ($\alpha>2$), the infection spreads like a front at linear speed and $I(t)$ grows like the volume $t^d$. The proofs bound first-passage distances $d_{\mathcal C}(u_0,v)$ above and below by powers $\|v\|^{s_\star\pm o(1)}$.

## Sources

- Z. Benjert, J. Komjáthy, J. Lengler, J. Lapinskas, "Degree-dependent and distance-dependent contact rates interpolate between explosive, exponential and polynomial epidemic growth", arXiv:2604.26939 (2026), Theorems 1 and 2, Definition of GIRG, Theorem 3, Corollary 4, Theorems 6 and 8, <https://doi.org/10.48550/arXiv.2604.26939>.
