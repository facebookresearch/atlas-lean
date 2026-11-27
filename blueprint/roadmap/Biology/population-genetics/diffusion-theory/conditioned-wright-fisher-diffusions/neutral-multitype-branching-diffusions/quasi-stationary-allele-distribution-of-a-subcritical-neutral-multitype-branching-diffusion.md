# Quasi-stationary allele distribution of a subcritical neutral multitype branching diffusion

**Model.** A neutral multitype branching diffusion on $\mathbb R_+^d$ has generator

$$\mathcal L = \frac12\sum_{i=1}^d x_i\partial_{x_i}^2 + \alpha\sum_{i=1}^d x_i\partial_{x_i} + \sum_{i,j=1}^d \gamma_{ji}x_j\partial_{x_i},$$

where $\alpha \in \mathbb R$ is the Malthusian growth parameter and $(\gamma_{ij})$ is an irreducible mutation rate matrix with stationary left eigenvector $\pi = (\pi_1,\dots,\pi_d)$. It is the diffusion limit of a Bienaymé–Galton–Watson process with offspring mean $\lambda \to 1$ in which each offspring of a type-$i$ parent has type $j$ with probability $r_{ij}$, with $\alpha = Y(0)\log\lambda/\sigma^2$ and $\gamma_{ij} = Y(0)(r_{ij} - \delta_{ij})/\sigma^2$. Write $\gamma_{ij} = \frac12\theta(P_{ij} - \delta_{ij})$ with a stochastic matrix $P$ and overall mutation rate $\theta$.

**Supercritical and critical limits.** If $\alpha > 0$, $\mathbf X(t)e^{-\alpha t}$ converges in law to a distribution concentrated on the ray $\{z\pi : z \ge 0\}$, its total mass having the single-type limit law. If $\alpha = 0$, $\mathbf X(t)/t$ conditioned on non-extinction converges to the law of $W\pi$ with $W$ exponential of density $2e^{-2w}$.

**Theorem (subcritical quasi-stationary law to first order in $\theta$).** For $\alpha < 0$ (normalized to $\alpha = -\tfrac12$), the Laplace transform $\zeta(\phi)$ of the quasi-stationary distribution (the Yaglom limit of $\mathbf X(t)$ given survival) satisfies, as $\theta \to 0$,

$$\zeta(\phi) = \sum_{i=1}^d \frac{\pi_i}{1+\phi_i} - \theta\sum_{i,j=1}^d \pi_jP_{ji}(1+\phi_i)\Big(\frac{1}{1+\phi_j} - \frac{1}{1+\phi_i}\Big)^2\frac{\log(1+\phi_i)}{\phi_i} + o(\theta).$$

At order zero the population is monomorphic: with probability $\pi_i$ all mass is of type $i$, with an $\mathrm{Exp}(1)$ size. At order $\theta$ the density has mass on coordinate axes and on two-dimensional faces (pairs of types), expressed through exponential integrals $E_1, E_2$.

**Corollary (moments and sampling distribution).** With harmonic numbers $H_n$, the quasi-stationary moments of the relative type frequencies $U_r = X_r/\sum_i X_i$ are $\mathbb E_{qs}[U_r^n] = \pi_r(1 - \theta(1 - P_{rr})H_{n-1}) + o(\theta)$. In a sample of $n$ individuals, the probability of the type configuration $\mathbf n$ is

$$p(n\mathbf e_r) = \pi_r\big(1 - \theta(1 - P_{rr})H_{n-1}\big) + O(\theta^2),\qquad p(n_r\mathbf e_r + n_s\mathbf e_s) = \theta\Big(\frac{\pi_rP_{rs}}{n_s} + \frac{\pi_sP_{sr}}{n_r}\Big) + O(\theta^2),$$

and configurations with more than two types have probability $O(\theta^2)$. This agrees to first order in $\theta$ with the sampling distribution of a constant-size Wright–Fisher diffusion with the same mutation structure.

## Expansion

Because mutation is neutral, the total mass $\sum_i X_i$ is a single-type Feller diffusion, and only the type composition feels the mutation matrix. In the growing cases mutation has infinite time to equilibrate the composition, so the limit collapses onto the eigenvector ray. In the subcritical case surviving populations are young and small, so composition is far from equilibrium: one solves the first-order PDE for the Laplace transform of the quasi-stationary law perturbatively in $\theta$, the zeroth-order solution being a mixture of single-type exponential laws. Inverting the Laplace transform and integrating against monomials gives the moments and, through Poisson sampling, the sampling formula, which matches the small-$\theta$ expansion of the Wright–Fisher stationary sampling law.

## Sources

- Conrad J. Burden and Robert C. Griffiths, "The stationary and quasi-stationary properties of neutral multi-type branching process diffusions", *Stochastic Models* 39 (2023), 185–218, <https://doi.org/10.1080/15326349.2022.2083167>. Numbering as in the preprint arXiv:2107.13197v3, <https://arxiv.org/abs/2107.13197v3>: Propositions 1–2 (Section 4), Theorems 1–2 (Section 5), Theorems 3–4 and Corollary 1 (Section 6).
