# Long-time behavior of the fast–slow protocell PDE

**Model.** A large population of protocells each contains two gene types: *fast* genes, which replicate faster inside the cell (advantage $s > 0$), and *slow* genes, which raise the protocell's own reproduction rate. Let $x \in [0,1]$ be the fraction of slow genes in a protocell and $f(t,x)$ the density of protocell compositions. Protocell-level reproduction is

$$G_{FS}(x) = x - \eta x^2, \qquad \eta \in [0,1],$$

so the collectively optimal composition is $x^* = \min\{1, 1/(2\eta)\}$. In the limit of many protocells, each with many genes, the two-level birth–death process gives

$$\frac{\partial f}{\partial t}(t,x) = \frac{\partial}{\partial x}\big[s\,x(1-x)\,f(t,x)\big] + \lambda\, f(t,x)\Big[G_{FS}(x) - \int_0^1 G_{FS}(y) f(t,y)\,dy\Big],$$

where $\lambda > 0$ is the relative strength of between-protocell to within-protocell competition. The equation is understood in the weak, measure-valued sense for $\mu_t(dx)$.

**Hölder exponent.** The initial measure $\mu_0$ has Hölder exponent $\theta \ge 0$ near $x = 1$ if $\theta = \inf\{\Theta \ge 0 : \lim_{x\to 0} \mu_0([1-x,1])/x^\Theta > 0\}$; it measures how much initial mass sits near the all-slow composition.

**Proposition.** Let $\mu_0$ have Hölder exponent $\theta > 0$ near $x=1$. As $t \to \infty$,

$$\mu_t(dx) \rightharpoonup \begin{cases} \delta(x), & \lambda(1-\eta) \le s\theta,\\[4pt] \tilde Z^{-1}\, x^{(\lambda/s)(1-\eta) - \theta - 1}(1-x)^{\theta - 1} \exp\!\Big(-\dfrac{\lambda\eta x}{s}\Big)\,dx, & \lambda(1-\eta) > s\theta,\end{cases}$$

with $\tilde Z$ a normalizing constant. Thus slow genes survive (coexistence of both types within protocells) exactly when between-protocell selection exceeds the threshold $\lambda^* = s\theta/(1-\eta)$; for $\eta = 1$ (all-fast and all-slow cells equally fit) coexistence is impossible at every $\lambda$.

## Proof sketch

This is the general multilevel replicator result for $\partial_t f = \partial_x[x(1-x)\pi(x) f] + \lambda f[G - \langle G\rangle]$ (with $\pi \equiv s$): along characteristics the within-cell flow pushes compositions toward $x = 0$ while the nonlocal term reweights them by relative protocell fitness. The Hölder exponent is conserved by the flow, and the solution converges to the unique steady density with that exponent when $\lambda[G(1) - G(0)] > \theta\,\pi(1)$, and to $\delta(x)$ otherwise. Here $G_{FS}(1) - G_{FS}(0) = 1 - \eta$ and $\pi(1) = s$, and the steady density solves a first-order linear ODE, giving the explicit Beta-type density with an exponential tilt.

## Sources

- Daniel B. Cooney, Fernando W. Rossine, Dylan H. Morris and Simon A. Levin, "A PDE Model for Protocell Evolution and the Origin of Chromosomes via Multilevel Selection", *Bulletin of Mathematical Biology* 84 (2022), 109, <https://doi.org/10.1007/s11538-022-01062-y>. Preprint version: arXiv:2109.09357 (2021), Section 2 (protocell PDE), Theorems on convergence to the steady density and to the delta function, and the long-time behavior proposition for the fast–slow model, <https://doi.org/10.48550/arXiv.2109.09357>.
