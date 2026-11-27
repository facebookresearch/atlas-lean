# Average dynamics of combined interaction graphs

**Setting.** A cellular system has continuous concentrations $\mathbf x \in \mathbb R^N$ of abundant species and discrete states $\sigma \in \Sigma$ of a few molecular machines (for example promoter or operator occupancy of genes); $\Sigma$ is often a product $\Sigma_1\times\cdots\times\Sigma_r$ of the machines' state spaces. In each discrete state the concentrations follow a deterministic vector field $f^{(\sigma)}(\mathbf x)$ (with its own deterministic interaction graph $\mathcal I_D$), while $\sigma$ jumps as a continuous-time Markov chain with generator $K(\mathbf x)$ whose rates depend on $\mathbf x$ (with interaction graph $\mathcal I_{MC}$ on $\Sigma$). The two scales are coupled through a master equation for the joint density.

**Average dynamics.** When the Markov chain is fast relative to the continuous dynamics (scaling parameter $\varepsilon \to 0$), the leading order of the $\varepsilon$-expansion of the joint density is a Liouville equation for a deterministic flow with vector field

$$\mathcal X[\mathbf x] = \sum_{\sigma\in\Sigma}\mu_\sigma(\mathbf x)\,f^{(\sigma)}(\mathbf x),$$

where $\mu(\mathbf x)$ is the invariant measure of the frozen chain $K(\mathbf x)$. The averaged interaction graph $\bar{\mathcal I}$ combines $\mathcal I_D$ and $\mathcal I_{MC}$.

**Propositions.**
1. *Long-time behaviour of the chain.* From any initial law $p_0$, $p(t) = p_0e^{Kt} \to \mu = \sum_l\theta_l\mu^{(l)}$, a convex combination of the extremal invariant measures of the closed classes.
2. *Uniqueness.* If $\mathcal I_{MC}$ has exactly one closed class (a single terminal strongly connected component), then $K$ has rank $|\Sigma| - 1$ and the invariant measure $\mu(\mathbf x)$, hence the average dynamics, is unique. Eigenvalues of $K$ are the eigenvalues of its diagonal blocks on the strongly connected components of $\mathcal I_{MC}$, so a unique terminal component gives a simple zero eigenvalue.
3. *Independent machines.* If the generator on $\Sigma_1\times\Sigma_2$ has the product form in which each machine's transition rates do not depend on the other's state, then the marginals $\mu_1, \mu_2$ of the joint invariant measure are invariant for the component chains $K_1, K_2$, and the machines act as independent subsystems.

Applied to gene regulation, this derives the macroscopic equations of feed-forward loops and genetic switches, with Hill-type or Michaelis–Menten-type rate laws arising as averages $\sum_\sigma\mu_\sigma(\mathbf x)f^{(\sigma)}(\mathbf x)$ over promoter states, together with the scalings under which they hold.

## Proof sketch

The averaging principle is the adiabatic elimination of the fast variable: on the fast time scale $\mathbf x$ is frozen and the chain relaxes to $\mu(\mathbf x)$; on the slow scale the drift seen by $\mathbf x$ is the $\mu(\mathbf x)$-average of the state-dependent drifts, and fluctuations vanish at leading order. For example, a gene with promoter states free/bound, binding rate $k_{\mathrm{on}}x^n$ and unbinding rate $k_{\mathrm{off}}$, produces protein at rate $\alpha$ only when free; then $\mu_{\mathrm{free}}(x) = k_{\mathrm{off}}/(k_{\mathrm{off}} + k_{\mathrm{on}}x^n)$ and the average dynamics is a repressive Hill function, as in models of the genetic toggle switch.

## Sources

- Markus Kirkilionis and Luca Sbano, "An averaging principle for combined interaction graphs: connectivity and applications to genetic switches", *Advances in Complex Systems* 13 (2010), 293–326, <https://doi.org/10.1142/s0219525910002669>. Preprint version: arXiv:0803.0635 (2008), average dynamics vector field, invariant-measure theorem, the $\star$-connectivity, strongly-connected-component and product-measure propositions, and the gene-regulation examples, <https://doi.org/10.48550/arXiv.0803.0635>.
