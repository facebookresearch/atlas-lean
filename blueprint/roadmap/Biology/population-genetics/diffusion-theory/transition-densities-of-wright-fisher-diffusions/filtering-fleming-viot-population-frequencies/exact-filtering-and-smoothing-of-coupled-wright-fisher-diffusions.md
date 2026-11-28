# Exact filtering and smoothing of coupled Wright–Fisher diffusions by duality

**Model.** At $L$ loci with $K_l$ alleles each, allele frequencies $\mathbf{x} = (\mathbf{x}^{(1)}, \dots, \mathbf{x}^{(L)})$ follow the [coupled Wright–Fisher (c-WF) diffusion](../../coupled-wright-fisher-diffusion-duality/coupled-wright-fisher-diffusion-with-pairwise-selection.md) with selection potential $V_{\boldsymbol\sigma,J}(\mathbf{x}) = \mathbf{x}^{\mathsf T}\boldsymbol\sigma + \frac12\mathbf{x}^{\mathsf T}J\mathbf{x}$ ($\boldsymbol\sigma$ single-locus selection, $J$ the symmetric block matrix of two-locus selection coefficients) and parent-independent mutation, the mutation drift at locus $l$ being $\mu_i^{(l)} = \frac12(\alpha_i^{(l)} - |\boldsymbol\alpha^{(l)}|x_i^{(l)})$, i.e. mutation rates $u^{(l)}_{ji} = \alpha^{(l)}_i/2$. Data are multinomial samples $\mathbf{Y}(t_n) \mid \mathbf{X}(t_n) = \mathbf{x} \sim \mathrm{MN}(\mathbf{N}_n, \mathbf{x})$ independently at each locus.

**Proposition (reversibility).** The c-WF diffusion is reversible with respect to its stationary law, the tilted product-Dirichlet law

$$p_{\boldsymbol\alpha,\boldsymbol\sigma,J}(d\mathbf{x}) = Z^{-1}\prod_{l,i}(x_i^{(l)})^{\alpha_i^{(l)} - 1}\,e^{2V_{\boldsymbol\sigma,J}(\mathbf{x})}\,d\mathbf{x}.$$

**Duality.** With $k(\mathbf{m}) = \mathbb{E}\big[\prod_{l,i}(\tilde X_i^{(l)})^{m_i^{(l)}}\big]$ under $p_{\boldsymbol\alpha,\boldsymbol\sigma,J}$ and $h(\mathbf{x},\mathbf{m}) = \mathbf{x}^{\mathbf{m}}/k(\mathbf{m})$, the diffusion is dual with duality function $h$ to the block-counting process $\mathbf{M}$ on $\mathbb{N}^K$ of [coupled ancestral selection graphs](../../coupled-wright-fisher-diffusion-duality/coupled-ancestral-selection-graphs-as-the-dual-of-the-coupled-wright-fisher-diffusion.md): $\mathbb{E}_{\mathbf{x}}[h(\mathbf{X}_t,\mathbf{m})] = \mathbb{E}_{\mathbf{m}}[h(\mathbf{x},\mathbf{M}_t)]$, where $\mathbf{M}$ coalesces and mutates within a locus and branches singly, or doubly across two loci at rates linear in $\boldsymbol\sigma$ and $J$.

**Proposition (filtering).** If $\mathbf{X}(t_n) \mid \mathbf{Y}(t_0{:}t_n) \sim \sum_{\mathbf{m}}\hat c_n(\mathbf{m})\,p_{\boldsymbol\alpha + \mathbf{m},\boldsymbol\sigma,J}$, then

$$\mathbf{X}(t_{n+1}) \mid \mathbf{Y}(t_0{:}t_n) \sim \sum_{\mathbf{n}} c_{n+1}(\mathbf{n})\,p_{\boldsymbol\alpha + \mathbf{n},\boldsymbol\sigma,J}, \qquad c_{n+1}(\mathbf{n}) \propto \sum_{\mathbf{m}}\hat c_n(\mathbf{m})\,p_{\mathbf{m},\mathbf{n}}(t_{n+1} - t_n),$$

with $p_{\mathbf{m},\mathbf{n}}(t)$ the transition probabilities of $\mathbf{M}$; conditioning on $\mathbf{Y}(t_{n+1}) = \mathbf{y}$ shifts each component to $p_{\boldsymbol\alpha + \mathbf{n} + \mathbf{y},\boldsymbol\sigma,J}$ with weights $\propto c_{n+1}(\mathbf{n})\,k(\mathbf{n} + \mathbf{y})/k(\mathbf{n})$. So filtering distributions remain countable mixtures of tilted Dirichlet laws. The marginal smoothing laws $\mathbf{X}(t_i) \mid \mathbf{Y}(t_0{:}t_n)$ are mixtures $\sum_{\mathbf{m},\mathbf{n}} w_i(\mathbf{m},\mathbf{n})\,p_{\boldsymbol\alpha + \mathbf{m} + \mathbf{n},\boldsymbol\sigma,J}$ with $w_i(\mathbf{m},\mathbf{n}) \propto \frac{k(\mathbf{m} + \mathbf{n})}{k(\mathbf{m})k(\mathbf{n})}\,\omega_{i+1}(\mathbf{m})\,\hat c_i(\mathbf{n})$. Here $\omega_{i+1}$ are the weights of the backward (cost-to-go) likelihood, $\mathbb{P}(\mathbf{Y}(t_{i+1}{:}t_n) \mid \mathbf{X}(t_i) = \mathbf{x}) = \sum_{\mathbf{m}}\omega_{i+1}(\mathbf{m})\,h(\mathbf{x},\mathbf{m})$, computed by the backward recursion $\omega_{n+1} = \delta_{\mathbf{0}}$ and

$$\omega_{i+1}(\mathbf{m}) = \sum_{\mathbf{n}}\omega_{i+2}(\mathbf{n})\,d_{i+1}(\mathbf{n},\mathbf{y}(t_{i+1}))\,p_{\mathbf{n} + \mathbf{y}(t_{i+1}),\mathbf{m}}(t_{i+1} - t_i), \qquad d_j(\mathbf{n},\mathbf{y}) = \int \mathrm{MN}(\mathbf{y};\mathbf{N}_j,\mathbf{x})\,h(\mathbf{x},\mathbf{n})\,p_{\boldsymbol\alpha,\boldsymbol\sigma,J}(d\mathbf{x}).$$

*Correction to the source.* The preprint prints the smoothing factor as $C_{\mathbf{m},\mathbf{n}} = k(\mathbf{m})k(\mathbf{n})/k(\mathbf{m} + \mathbf{n})$, from the identity $h(\mathbf{x},\mathbf{m})h(\mathbf{x},\mathbf{n}) = C_{\mathbf{m},\mathbf{n}}\,h(\mathbf{x},\mathbf{m} + \mathbf{n})$. Since $h(\mathbf{x},\mathbf{m})h(\mathbf{x},\mathbf{n}) = \mathbf{x}^{\mathbf{m} + \mathbf{n}}/(k(\mathbf{m})k(\mathbf{n})) = \frac{k(\mathbf{m} + \mathbf{n})}{k(\mathbf{m})k(\mathbf{n})}\,h(\mathbf{x},\mathbf{m} + \mathbf{n})$, the printed factor is the reciprocal of the correct one; the statement above uses the corrected factor, and the rest of the source's proof goes through unchanged.

## Depends on

- [Coupled Wright–Fisher diffusion with pairwise selection](../../coupled-wright-fisher-diffusion-duality/coupled-wright-fisher-diffusion-with-pairwise-selection.md)
- [Coupled ancestral selection graphs as the dual of the coupled Wright–Fisher diffusion](../../coupled-wright-fisher-diffusion-duality/coupled-ancestral-selection-graphs-as-the-dual-of-the-coupled-wright-fisher-diffusion.md)

## Expansion

Detailed balance holds because the drift is the Wright–Fisher divergence term plus $D\nabla V$, a gradient flow in the metric $D^{-1}$, so the Gibbs tilt $e^{2V}$ of the neutral Dirichlet law is invariant and reversible. Multinomial likelihoods are conjugate to the tilted Dirichlet family, and the duality $\mathbb{E}_{\mathbf{x}}[h(\mathbf{X}_t,\mathbf{m})] = \mathbb{E}_{\mathbf{m}}[h(\mathbf{x},\mathbf{M}_t)]$ propagates each mixture component $h(\cdot,\mathbf{m})\,p_{\boldsymbol\alpha,\boldsymbol\sigma,J}$ forward in time as a mixture over the dual's states. Since $\mathbf{M}$ can branch, its transition probabilities and the constants $k(\mathbf{m})$ have no closed form and are approximated by Monte Carlo in practice.

## Sources

- Chiara Boetti and Matteo Ruggiero, "Filtering coupled Wright–Fisher diffusions", *Journal of Mathematical Biology* 89 (2024), 64, <https://doi.org/10.1007/s00285-024-02156-y>. Numbering as in the preprint arXiv:2410.11429v1, <https://arxiv.org/abs/2410.11429v1>: Section 2 (Proposition 2.1 on reversibility, and duality in Section 2.3) and Section 3 (Propositions 3.1 and 3.2 on filtering and smoothing; the factor $C_{\mathbf{m},\mathbf{n}}$ in Proposition 3.2 is printed inverted, corrected here as explained above; the backward recursion for $\omega$ and its base case are read off the proof of Proposition 3.2).
