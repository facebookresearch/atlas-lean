# Local stability of perfect alignment in the midpoint kinetic model of collective motion

**Model.** Individuals (e.g. animals in a flock) carry a direction of motion $x \in \mathbb S^2$; spatial positions are ignored (spatially homogeneous regime). At rate $1$ an individual meets a random partner and both adopt a new common direction drawn from a collision kernel $K(\cdot, x_*, x_*')$. In the large-population limit the law $\rho_t$ of directions solves the Boltzmann-type equation

$$\partial_t \rho(t,x) = \int_{\mathbb S^2 \times \mathbb S^2} K(x, x_*, x_*')\,\rho(t,x_*)\,\rho(t,x_*')\,dx_*\,dx_*' - \rho(t,x).$$

In the **midpoint model** $K(\cdot, x_*, x_*') = \delta_{x_m}$ with $x_m = (x_* + x_*')/\|x_* + x_*'\|$ whenever $x_* \ne -x_*'$, and for antipodal pairs $K(\cdot, x_*, -x_*)$ is any probability measure supported on the great circle $\{x : x \cdot x_* = 0\}$. Global alignment of the population is a Dirac mass $\delta_{x_0}$, which is a stationary solution for every $x_0$. Distances between laws are measured with the quadratic Wasserstein distance $W_2$.

**Theorem.** There are $C_1 > 0$ and $\eta > 0$ such that every solution $\rho \in C(\mathbb R_+, \mathcal P(\mathbb S^2))$ with $W_2(\rho_0, \delta_{x_0}) < \eta$ for some $x_0 \in \mathbb S^2$ converges to a perfectly aligned state: there is $x_\infty \in \mathbb S^2$ with

$$W_2(\rho_t, \delta_{x_\infty}) \le C_1\,W_2(\rho_0, \delta_{x_0})\,e^{-t/4} \quad \text{for all } t \ge 0.$$

The limiting direction $x_\infty$ need not equal $x_0$, since nothing is conserved on the sphere. In $\mathbb R^n$ the same model conserves the center of mass $\bar x$ and contracts exactly: $W_2(\delta_{\bar x}, \rho_t) = W_2(\delta_{\bar x}, \rho_0)\,e^{-t/4}$. The local result extends to complete Riemannian manifolds with bounded curvature and positive injectivity radius, and to non-midpoint kernels satisfying a contraction condition with parameter $\beta < 1$, with rate $e^{-(1-\beta)t/4}$.

## Expansion

On the sphere the model has neither a conserved quantity nor an energy that decreases for all initial data, so the proof uses the pair energy $E(\rho) = \iint d(x,y)^2\,d\rho(x)\,d\rho(y)$ (geodesic distance $d$), which dominates $W_2(\rho, \delta_{\bar x})^2$ for a suitable center $\bar x$, and shows that it is a local Lyapunov function: near Dirac masses, $\tfrac12 \tfrac{d}{dt}E(\rho) \le -\tfrac14 E(\rho) + C_0 E(\rho)^{1+\gamma}$, because replacing two directions by their geodesic midpoint shrinks squared distances by a factor $1/4$ up to curvature corrections controlled by Rauch and Toponogov comparison theorems. This gives exponential decay of $E$ while it is small, and controlling the motion of the center shows it converges to some $x_\infty$, yielding the $W_2$ estimate.

## Sources

- Pierre Degond, Amic Frouvelle, Gaël Raoul, "Local stability of perfect alignment for a spatially homogeneous kinetic model", arXiv (2014). Equation of Section 1 (kinetic model), Assumption 3.1 (midpoint models on the sphere), Proposition 2.3, Theorem 3.2, Proposition 3.8, Theorems 4.3 and 5.9. <https://doi.org/10.48550/arXiv.1403.5233>. Published version: Journal of Statistical Physics 157(1) (2014), 84–112, <https://doi.org/10.1007/s10955-014-1062-3>; locators above refer to the arXiv version.
