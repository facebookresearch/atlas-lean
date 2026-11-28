# Bursty protein network model and its master equation

**Model.** A gene regulatory network on $n$ genes has protein levels $P = (P_1, \dots, P_n) \in \mathbb{R}_+^n$. Each protein degrades deterministically and is produced in bursts:

$$P_i'(t) = -d_{1,i}\, P_i(t) \quad \text{between bursts}, \qquad P_i \to P_i + \mathcal E(c_i) \quad \text{at rate } k^\theta_{\mathrm{on},i}(P),$$

where $\mathcal E(c_i)$ is an exponential burst size with rate $c_i$ (mean $1/c_i$), drawn independently. The burst-rate functions encode the network $\theta = (\theta_{ij})$:

$$k^\theta_{\mathrm{on},i}(P) = k_{0,i} + (k_{1,i} - k_{0,i})\,\sigma_i^\theta(P), \qquad \sigma^\theta_i(P) = \Big(1 + \exp\big(-\beta_i - \textstyle\sum_{j} \theta_{ij} P_j\big)\Big)^{-1},$$

with $0 < k_{0,i} < k_{1,i}$, basal activity $\beta_i$, and $\partial k^\theta_{\mathrm{on},i}/\partial P_j$ having the sign of $\theta_{ij}$ (activation or repression $j \to i$). This is a piecewise-deterministic Markov process obtained from a two-stage mRNA–protein bursting model when mRNA degradation is much faster than protein degradation.

**Master equation.** The density $u(t, x)$ of $P(t)$ satisfies the integro-differential equation

$$\partial_t u(t,x) = \sum_{i=1}^n \Big[ \partial_{x_i}\big(d_{1,i} x_i\, u(t,x)\big) + \int_0^{x_i} k^\theta_{\mathrm{on},i}(x - h e_i)\, u(t, x - h e_i)\, c_i e^{-c_i h}\, dh - k^\theta_{\mathrm{on},i}(x)\, u(t,x) \Big].$$

**Deterministic limit and basins.** Let $\varepsilon$ be the ratio of the typical protein degradation rate to the typical burst rate. As $\varepsilon \to 0$, trajectories on finite time intervals converge in probability to solutions of

$$P_i' = \frac{k^\theta_{\mathrm{on},i}(P)}{c_i} - d_{1,i} P_i, \qquad i = 1, \dots, n,$$

whose stable equilibria (attractors) $P_z$, solving $P_i = k^\theta_{\mathrm{on},i}(P)/(c_i d_{1,i})$, have basins $Z = \{z_1, \dots, z_m\}$ identified with cell types. For small $\varepsilon$ transitions between basins are rare events on time scales of order $e^{C/\varepsilon}$.

**Single-gene stationary law.** For one gene with constant burst rate $k$, the unique stationary distribution is $\mathrm{Gamma}(k/d_1, c)$ (shape $k/d_1$, rate $c$), with mean $k/(c\, d_1)$, matching the deterministic equilibrium.

## Expansion

The drift term $\partial_{x_i}(d_{1,i}x_i u)$ is the Liouville transport for exponential decay; the integral is the inflow of probability from states $x - he_i$ that burst by $h$ (density $c_i e^{-c_i h}$), and the last term is the outflow from $x$ at rate $k_{\mathrm{on},i}$. Replacing the jump term by its mean $k_{\mathrm{on},i}(P)/c_i$ gives the deterministic limit. For one gene with constant $k$, substituting $u(x) \propto x^{a-1}e^{-cx}$ with $a = k/d_1$ into the stationary equation, the inflow integral equals $(k c x/a)\,u(x)$, the transport term equals $d_1(a - cx)\,u(x)$ and the outflow is $-k\,u(x)$, which sum to zero when $a = k/d_1$; uniqueness follows from the one-dimensional structure.

## Sources

- E. Ventre, "Reverse engineering of a mechanistic model of gene expression using metastability and temporal dynamics", *In Silico Biology* 14(3–4) (2021) 89–113. Section 2 (two-stage bursting model, Eq. (1); burst-rate functions, Eq. (2); reduced protein model, Eq. (3)), Section 2.3 (deterministic limit, Eqs. (4)–(5); rare transitions between basins), Section 3.1 (single-gene Gamma stationary law), and Appendix B (master equation, Eq. (18)). <https://doi.org/10.3233/isb-210226>. PMCID: PMC8842760.
