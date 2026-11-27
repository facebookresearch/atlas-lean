# Large deviation principle for jump-Markov processes on sparse spatial networks and SIS transition paths

**Setting.** $N$ nodes have positions $x^j_N$ on a compact Riemannian manifold $\mathcal{E}$, with empirical position measure converging weakly to $\kappa$. Node $j$ has a state $\sigma^j(t)$ in a finite set $\Gamma$. Connections $J^{jk} \in \{-1,0,1\}$ are sampled independently (or symmetrically) with $\mathbb{P}(J^{jk} = \pm 1) = \phi_N p_\pm(x^j_N, x^k_N)$ for Lipschitz $p_\pm$, where the sparsity $\phi_N \to 0$ satisfies $N e^{-cN\phi_N}$ bounded for every $c > 0$; set $\mathcal{J} = p_+ - p_-$. Node $j$ jumps from its current state to $\alpha$ at rate $f_\alpha(x^j_N, \sigma^j(t), w^j(t))$, where $w^j_\beta(t) = (N\phi_N)^{-1}\sum_k J^{jk}\mathbf{1}\{\sigma^k(t) = \beta\}$ is the local field. Initial empirical laws $\hat\nu^N_0$ of (state, position) converge to some $\nu_0$ with densities $q_0(\alpha,\cdot)$.

**Theorem (law of large numbers).** The empirical process converges to the unique solution of

$$\frac{d}{dt}q_t(\alpha,\theta) = \sum_{\beta:(\beta,\alpha)\in\Xi} f_\alpha(\theta,\beta,w_t(\theta))\,q_t(\beta,\theta) - \sum_{\beta:(\alpha,\beta)\in\Xi} f_\beta(\theta,\alpha,w_t(\theta))\,q_t(\alpha,\theta),\qquad w_{t,\beta}(\theta) = \int_{\mathcal{E}}\mathcal{J}(\theta,y)\,q_t(\beta,y)\,\kappa(dy),$$

where $\Xi$ is the set of allowed transitions.

**Theorem (large deviations).** The empirical reaction-flux measures $\hat\mu^N$ (and hence the empirical occupation-measure paths $\hat\nu^N$) satisfy a large deviation principle at speed $N$ with good rate functions $\mathcal{G}$ (resp. $\mathcal{H}$): for closed $\mathcal{A}$ and open $\mathcal{O}$,

$$\limsup_{N\to\infty} \frac1N\log\mathbb{P}(\hat\nu^N \in \mathcal{A}) \le -\inf_{\mathcal{A}}\mathcal{H}, \qquad \liminf_{N\to\infty}\frac1N\log\mathbb{P}(\hat\nu^N \in \mathcal{O}) \ge -\inf_{\mathcal{O}}\mathcal{H}.$$

The rate function is the same as for the network in which every node interacts with every other through the kernel $\mathcal{J}$ (all-to-all connectivity): the sparse disorder does not change large deviations at this scale.

**Application (spatial SIS).** On $\mathcal{E} = \mathbb{S}^1$ with symmetric connection probability $\phi_N\mathcal{J}$, a susceptible node is infected at rate $\beta N^{-1}\sum_k J^{jk}\mathbf{1}\{\sigma^k = I\}$ (with the sparse normalization) and an infected node recovers at rate $\alpha$. The susceptible density $s(t,\theta)$ obeys $\partial_t s = -\beta s\int_{\mathcal{E}}\mathcal{J}(\theta,\tilde\theta)(1 - s(t,\tilde\theta))\,d\tilde\theta + \alpha(1-s)$, and the path rate function is

$$\mathcal{H}_T(s) = \int_0^T\!\!\int_{\mathcal{E}} L_\theta(\dot s(t,\theta), s(t))\,d\theta\,dt,\qquad L_\theta(\dot s, s) = \inf_{\substack{a,b \ge 0\\ \dot s = b - a}}\Big\{\lambda_\theta(s)\,\ell\Big(\frac{a}{\lambda_\theta(s)}\Big) + \alpha(1-s(\theta))\,\ell\Big(\frac{b}{\alpha(1-s(\theta))}\Big)\Big\},$$

with $\lambda_\theta(s) = \beta s(\theta)\int\mathcal{J}(\theta,\tilde\theta)(1 - s(\tilde\theta))\,d\tilde\theta$ and $\ell(x) = x\log x - x + 1$. A twice-differentiable minimizer between prescribed endpoint states satisfies an explicit second-order Euler–Lagrange integro-differential equation, which determines the most likely transition path (e.g. noise-driven extinction or re-emergence).

## Expansion

Each node's transitions are Poisson processes modulated by a local field. The key estimate is that, under the averaging hypothesis $N^{-1}\sum_j \sup_{\alpha\in\{-1,0,1\}^N}\big|\sum_k(\phi_N^{-1}J^{jk} - \mathcal{J}(x^j,x^k))\alpha^k\big| \to 0$, which holds with probability tending to one for independently sampled sparse edges with $N\phi_N \gg \log N$, the local fields are uniformly close to the graphon fields $w_t(\theta)$ on exponentially likely events, so the sparse network is exponentially equivalent to the all-to-all one. The LDP for the all-to-all, spatially discretized system follows from Sanov-type and contraction arguments for Poisson fluxes, giving rate functions of the form $\int \lambda\,\ell(\text{flux}/\lambda)$, and a projective limit removes the spatial discretization.

## Sources

- James MacLaurin, "Large deviations of mean-field jump-Markov processes on structured sparse random graphs", Stochastic Processes and their Applications 199 (2026), 104930, <https://doi.org/10.1016/j.spa.2026.104930>; numbering as in arXiv:2410.13682: Section 2 (hypotheses, Theorems 2–3 and Corollary 5), Theorems 7, 11–12 (Section 3) and the SIS application with Theorem 20 (Section 4).
