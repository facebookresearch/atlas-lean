# Anderson–Chaplain chemotaxis–haptotaxis model of angiogenesis

**Model.** On a bounded domain $\Omega \subset \mathbb{R}^d$ ($d = 1, 2$) between a parent vessel and a tumour, let $n(x, t)$ be the density of endothelial (tip) cells, $c(x, t)$ the concentration of tumour angiogenic factor (TAF) and $f(x, t)$ the concentration of fibronectin in the extracellular matrix. In nondimensional variables,

$$\frac{\partial n}{\partial t} = D \nabla^2 n - \nabla \cdot \bigl(\chi(c)\, n \nabla c\bigr) - \nabla \cdot \bigl(\rho\, n \nabla f\bigr),$$

$$\frac{\partial f}{\partial t} = \beta n - \gamma n f, \qquad \frac{\partial c}{\partial t} = -\eta n c,$$

with chemotactic sensitivity

$$\chi(c) = \frac{\chi}{1 + \alpha c},$$

positive constants $D, \chi, \alpha, \rho, \beta, \gamma, \eta$, no-flux boundary conditions $\nu \cdot \bigl(D\nabla n - \chi(c) n \nabla c - \rho n \nabla f\bigr) = 0$ on $\partial\Omega$, and initial data in which TAF is highest at the tumour, fibronectin is roughly uniform or highest near the parent vessel, and endothelial cells are concentrated at the parent vessel.

Here $D \nabla^2 n$ is random motility, the second term chemotaxis up TAF gradients with a sensitivity that decreases as receptors saturate, and the third term haptotaxis up fibronectin gradients. Fibronectin is produced by endothelial cells ($\beta n$) and bound or degraded on contact ($\gamma n f$); TAF diffuses little on the time scale of migration and is consumed by the cells ($\eta n c$).

## Expansion

The $n$-equation is in divergence form with no proliferation term, so under the no-flux condition the total cell number $\int_\Omega n\,dx$ is conserved; nonnegative initial data keep $n$, $c$ and $f$ nonnegative, and $c$ is nonincreasing in time at every point, so the chemotactic drive weakens where cells have consumed TAF. Without haptotaxis ($\rho = 0$) cells migrate up the TAF gradient toward the tumour. Because fibronectin is produced by the cells themselves, haptotaxis adds a self-generated adhesive cue that keeps migrating cells together and counteracts purely chemotactic spreading; the balance of the two taxis terms controls whether and how fast the front reaches the tumour. A discretization of the $n$-equation whose five-point stencil coefficients are read as probabilities of an individual tip cell moving left, right, up, down or staying gives a biased random walk of tip cells; adding rules for branching and anastomosis and recording the trail behind each tip turns this into a discrete model of capillary networks. The same chemotaxis–haptotaxis structure was later adapted to wound-healing angiogenesis.

## Sources

- J. A. Flegg, S. N. Menon, H. M. Byrne et al., "A current perspective on wound healing and tumour-induced angiogenesis", Bulletin of Mathematical Biology (2020), <https://doi.org/10.1007/s11538-020-00696-0>. Section 3 (early and hybrid continuum–discrete models of angiogenesis).
- A. R. A. Anderson and M. A. J. Chaplain, "Continuous and discrete mathematical models of tumor-induced angiogenesis", Bulletin of Mathematical Biology 60 (1998), <https://doi.org/10.1006/bulm.1998.0042>.
