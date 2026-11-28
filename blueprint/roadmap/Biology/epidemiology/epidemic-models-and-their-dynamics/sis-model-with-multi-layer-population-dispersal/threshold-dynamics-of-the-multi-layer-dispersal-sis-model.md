# Threshold dynamics of the SIS model with multi-layer population dispersal

Consider $n$ patches and $m$ classes of individuals; class $\alpha$ moves between patches by a continuous-time Markov chain with generator $Q^\alpha$ on a digraph $\mathcal{G}^\alpha$, and within patch $i$ individuals of class $\alpha$ are infected at rate $\beta_i^\alpha > 0$ and recover at rate $\delta_i^\alpha \ge 0$. Let $x_i^\alpha$ be the number of class-$\alpha$ individuals in patch $i$ and $p_i^\alpha \in [0,1]$ their infected fraction, stacked into $\mathbf{p} \in [0,1]^{nm}$, $P = \operatorname{diag}(\mathbf{p})$, $B = \operatorname{diag}(\beta_i^\alpha)$, $D = \operatorname{diag}(\delta_i^\alpha)$. Let $F(\mathbf{x}) = \mathbf{1}_m \otimes [F^1,\dots,F^m]$ with $F^\alpha = \operatorname{diag}\big(x_i^\alpha/\sum_{\alpha'} x_i^{\alpha'}\big)$, and $L(\mathbf{x}) = \oplus_\alpha L^\alpha(\mathbf{x})$ with $l^\alpha_{ii} = \sum_{k \ne i} q^\alpha_{ki} x^\alpha_k/x^\alpha_i$ and $l^\alpha_{ij} = -q^\alpha_{ji} x^\alpha_j/x^\alpha_i$ for $i \ne j$. If every $\mathcal{G}^\alpha$ is strongly connected, the dynamics are

$$
\dot{\mathbf{p}} = \big(BF(\mathbf{x}) - D - L(\mathbf{x})\big)\mathbf{p} - P\,BF(\mathbf{x})\,\mathbf{p}, \qquad \dot{\mathbf{x}}^\alpha = (Q^\alpha)^\top \mathbf{x}^\alpha .
$$

Let $\boldsymbol{\pi}$ be the stationary population distribution, $F^* = F(\boldsymbol\pi)$, $L^* = L(\boldsymbol\pi)$, and let $\mu(\cdot)$ denote the spectral abscissa (largest real part of an eigenvalue).

**Theorem.** Under strong connectivity of every layer:

1. $[0,1]^{nm}$ is forward invariant, and $\mathbf{p}(0) > \mathbf{0}$ implies $\mathbf{p}(t) \gg \mathbf{0}$ for $t > 0$.
2. $(\mathbf{0}, \boldsymbol\pi)$ is a disease-free equilibrium; it is globally asymptotically stable if and only if $\mu(BF^* - D - L^*) \le 0$, and unstable otherwise.
3. An endemic equilibrium $(\mathbf{p}_{\mathrm{end}}, \boldsymbol\pi)$ with $\mathbf{p}_{\mathrm{end}} \gg \mathbf{0}$ exists if and only if $\mu(BF^* - D - L^*) > 0$, and it is then almost globally asymptotically stable with region of attraction $[0,1]^{nm} \setminus \{\mathbf{0}\}$.

When layers are not strongly connected, the same dichotomy holds for the reduced model on the sink nodes of each layer, with the corresponding reduced matrices.

## Expansion

The population equation is linear and converges to $\boldsymbol\pi$, so the infection equation is asymptotically autonomous with linearization $BF^* - D - L^*$ at $\mathbf{p} = \mathbf{0}$. This matrix is Metzler and irreducible, so its spectral abscissa is a Perron eigenvalue; when it is non-positive, a positive left eigenvector gives a linear Lyapunov function for the disease-free state. When it is positive, monotonicity and concavity of the SIS vector field (as in the single-layer Lajmanovich–Yorke model) give a unique positive fixed point, attracting every nonzero initial condition. Multi-layer dispersal enters only through the effective mixing weights $F^*$ and the mobility Laplacian $L^*$.

## Sources

- Vishal Abhishek and Vaibhav Srivastava, *SIS Epidemic Spreading under Multi-layer Population Dispersal in Patchy Environments*, arXiv:2211.00169, Proposition 1 (Section 2), Theorem 2 (Section 3) and Corollaries 5 and 6 (Section 4). <https://doi.org/10.48550/arXiv.2211.00169> Published version: IEEE Transactions on Control of Network Systems 11 (2024) 126–138, <https://doi.org/10.1109/tcns.2023.3272839>.
