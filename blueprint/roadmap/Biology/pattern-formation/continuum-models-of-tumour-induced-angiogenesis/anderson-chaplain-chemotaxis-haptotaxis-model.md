# Anderson–Chaplain chemotaxis–haptotaxis model of angiogenesis

**Model.** On a bounded domain $\Omega \subset \mathbb{R}^d$ ($d = 1, 2$) between a parent vessel and a tumour, let $n(x, t)$ be the density of endothelial (tip) cells, $c(x, t)$ the concentration of tumour angiogenic factor (TAF) and $f(x, t)$ the concentration of fibronectin in the extracellular matrix. In nondimensional variables,

$$\frac{\partial n}{\partial t} = D \nabla^2 n - \nabla \cdot \bigl(\chi(c)\, n \nabla c\bigr) - \nabla \cdot \bigl(\rho\, n \nabla f\bigr),$$

$$\frac{\partial f}{\partial t} = \beta n - \gamma n f, \qquad \frac{\partial c}{\partial t} = -\eta n c,$$

with chemotactic sensitivity

$$\chi(c) = \frac{\chi}{1 + \alpha c},$$

positive constants $D, \chi, \alpha, \rho, \beta, \gamma, \eta$, no-flux boundary conditions $\nu \cdot \bigl(D\nabla n - \chi(c) n \nabla c - \rho n \nabla f\bigr) = 0$ on $\partial\Omega$, and initial data in which TAF is highest at the tumour, fibronectin is roughly uniform or highest near the parent vessel, and endothelial cells are concentrated at the parent vessel.

Here $D \nabla^2 n$ is random motility, the second term chemotaxis up TAF gradients with a sensitivity that decreases as receptors saturate, and the third term haptotaxis up fibronectin gradients. Fibronectin is produced by endothelial cells ($\beta n$) and bound or degraded on contact ($\gamma n f$). TAF is consumed by the cells ($\eta n c$) and has no diffusion term: the model starts from an initially established TAF profile and neglects TAF diffusion during migration. This is a modelling assumption, not a claim derived here about physical diffusion time scales.

## Expansion

The $n$-equation is in divergence form with no proliferation term, so under the no-flux condition the total cell number $\int_\Omega n\,dx$ is conserved. For smooth solutions with nonnegative initial data, $n$ stays nonnegative, and then $c(x, t) = c(x, 0)\exp\bigl(-\eta\int_0^t n(x, s)\,ds\bigr)$ and $f$ stay nonnegative, and $c$ is nonincreasing in time at every point. Pointwise depletion does not imply a weaker chemotactic term: differentiating the $c$-equation gives $\partial_t \nabla c = -\eta\,(n \nabla c + c \nabla n)$, and the term $c\nabla n$ can steepen $\nabla c$ where cells accumulate, while the sensitivity $\chi(c)$ increases as $c$ falls. Without haptotaxis ($\rho = 0$) cells migrate up the TAF gradient toward the tumour. Because fibronectin is produced by the cells themselves, haptotaxis adds a self-generated adhesive cue that keeps migrating cells together and counteracts purely chemotactic spreading; the balance of the two taxis terms controls whether and how fast the front reaches the tumour. An explicit five-point discretization of the $n$-equation in two dimensions writes $n$ at the next time step as a combination of its values at a grid point and its four neighbours, with coefficients $P_0$ (stay) and $P_1, \dots, P_4$ (left, right, down, up) that depend on $c$, $f$ and the step sizes. These coefficients need not be probabilities: already for pure diffusion the central coefficient is $1 - 4D\Delta t/h^2$, which is negative when $\Delta t > h^2/(4D)$. When the step sizes make all five coefficients nonnegative with a positive sum, dividing each by their sum gives the probabilities of an individual tip cell staying or moving left, right, down or up, and so a biased random walk of tip cells; adding rules for branching and anastomosis and recording the trail behind each tip turns this into a discrete model of capillary networks. The same chemotaxis–haptotaxis structure was later adapted to wound-healing angiogenesis.

## Sources

- J. A. Flegg, S. N. Menon, H. M. Byrne et al., "A current perspective on wound healing and tumour-induced angiogenesis", Bulletin of Mathematical Biology (2020), <https://doi.org/10.1007/s11538-020-00696-0>. Section 3 (early and hybrid continuum–discrete models of angiogenesis).
- A. R. A. Anderson and M. A. J. Chaplain, "Continuous and discrete mathematical models of tumor-induced angiogenesis", Bulletin of Mathematical Biology 60 (1998), <https://doi.org/10.1006/bulm.1998.0042>.
