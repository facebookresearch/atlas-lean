# Fourth-order reduction and logarithmic kernel of the equilibrating signalling cascade

**Model.** Cells of density $u$ produce an intermediate substance $w$, which produces the chemoattractant $c$ sensed by the cells. With $\chi, \tau > 0$, the fully equilibrating **parabolic-elliptic-elliptic (PES) cascade** is

$$\partial_t u = \Delta u - \chi\nabla\cdot(u\nabla c), \qquad 0 = \Delta w - w + u, \qquad 0 = \tau\Delta c - c + w,$$

posed on $\mathbb{R}^N$, on $\mathbb{T}^N$, or on a bounded $C^2$ domain with homogeneous Neumann conditions. The **mixed elliptic-parabolic (MEP) cascade** replaces the last equation by $\partial_t c = \Delta c - c + w$. Write $A = I - \Delta$ and $A_\tau = I - \tau\Delta$.

**Theorem.**
1. (Reduction) PES reduces to $\partial_t u = \Delta u - \chi\nabla\cdot(u\nabla K_\tau u)$ with $K_\tau = A_\tau^{-1}A^{-1}$, whose Fourier multiplier is $\big((1+|\xi|^2)(1+\tau|\xi|^2)\big)^{-1}$. $K_\tau$ is positive and self-adjoint on $L^2$, and it is a smoothing operator of principal order $-4$ with principal part $\tau^{-1}(-\Delta)^{-2}$.
2. (Scaling) The high-frequency scaling of PES is $u_\lambda(x,t) = \lambda^4 u(\lambda x, \lambda^2 t)$, so the scaling-critical Lebesgue exponent is $q_c = N/4$ and the mass-critical dimension is $N = 4$ (instead of $N = 2$ for the classical Keller-Segel system).
3. (Logarithmic kernel) On $\mathbb{R}^4$ the kernel of $K_\tau$ satisfies

$$G_\tau(x) = \frac{1}{8\pi^2\tau}\log\frac{1}{|x|} + R_\tau(x),$$

with $R_\tau$ locally bounded; the same interior expansion holds on $\mathbb{T}^4$ and in smooth bounded Neumann domains.
4. (Memory) MEP does not reduce to a static operator: eliminating $w$ and $c$ gives a Volterra (time-memory) drift whose near-diagonal limit has principal order $-1$, as in the two-dimensional Keller-Segel problem, so PES-type static scaling does not determine its criticality.

**Candidate critical mass.** PES is the $L^2$-Wasserstein-type gradient flow of $\mathcal{F}[u] = \int u\log u - \frac{\chi}{2}\int uK_\tau u$, with $\frac{d}{dt}\mathcal{F} = -\int u|\nabla(\log u - \chi K_\tau u)|^2 \le 0$. For a one-point concentrating profile of mass $M$ in $N = 4$, $\mathcal{F}[u_\varepsilon] = \big(4M - \frac{\chi M^2}{16\pi^2\tau}\big)\log\frac{1}{\varepsilon} + O(1)$, which changes sign at $M_* = 64\pi^2\tau/\chi$, the analogue of $8\pi/\chi$ in two dimensions.

## Expansion

The fourth-order symbol arises because two second-order resolvents are composed: $\frac{1}{(1+|\xi|^2)(1+\tau|\xi|^2)} = \frac{1}{\tau|\xi|^4} + O(|\xi|^{-6})$. The fundamental solution of $(-\Delta)^2$ in $\mathbb{R}^4$ is $\frac{1}{8\pi^2}\log\frac{1}{|x|}$, so in four dimensions the Newtonian-type singularities cancel and only a logarithm remains, exactly the structure that makes the logarithmic Hardy-Littlewood-Sobolev inequality sharp for Keller-Segel in two dimensions. The concentration computation balances entropy, which contributes $4M\log\frac{1}{\varepsilon}$ under $\varepsilon^{-4}$ rescaling, against the logarithmic interaction energy. $M_*$ is a scaling candidate; proving it is the sharp threshold requires an adapted Adams-type inequality.

## Sources

- Jiguang Yu and Louis Shuo Wang, "Structural dichotomy and mass criticality in indirect chemotaxis cascades: fourth-order ellipticity versus Volterra memory", arXiv:2605.30438 (2026), Section 1, Theorem 1.2, and Section 2, Propositions 2.2, 2.3 and 2.6, <https://doi.org/10.48550/arXiv.2605.30438>.
