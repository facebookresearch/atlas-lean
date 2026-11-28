# Conditional construction of a calibrated tree prior

**Setting.** $\mathcal{G}$ is the space of time trees (genealogies) $g = \{\psi, h\}$ on $n$ taxa, with ranked topology $\psi$ and internal node heights $h$. Let $f_G$ be a tree prior density on $\mathcal{G}$ (e.g. Yule with birth rate $\lambda$), possibly restricted to trees in which a taxon set $\varphi$ is monophyletic. Let $\tau(g)$ be the age of the most recent common ancestor of $\varphi$, let

$$f_T(x) = \int_{\mathcal{G}} \mathbf{1}\big(\tau(g) = x\big)\, f_G(g)\, dg$$

be the marginal density of $\tau$ under $f_G$, and let $\rho_T$ be a desired calibration density on $\tau$.

**Desired properties.**

- (I) The marginal density of the calibrated age equals the calibration density: $\int_{\mathcal{G}} \mathbf{1}(\tau(g) = x)\,\rho_G(g)\,dg = \rho_T(x)$.
- (II) Among trees with equal calibrated age, $\rho_G$ is proportional to $f_G$: $\tau(g_1) = \tau(g_2) \Rightarrow \rho_G(g_1)/\rho_G(g_2) = f_G(g_1)/f_G(g_2)$.

**Proposition (conditional construction).** The density

$$\rho_G(g) = f_G(g)\,\frac{\rho_T(\tau(g))}{f_T(\tau(g))} \qquad \text{(Eq. 4)}$$

integrates to $1$ and satisfies (I) and (II); informally, $\rho_G(g) = f_G(g \mid \tau(g))\,\rho_T(\tau(g))$.

**Contrast with the multiplicative construction.** The product $f_G(g)\,\rho_T(\tau(g))$ (normalized) generally has a marginal on $\tau$ proportional to $f_T(x)\rho_T(x)$, not $\rho_T(x)$, and can induce a non-uniform prior on topologies even when $f_G$ is uniform on them.

**Special case.** Under the Yule prior, the age at which a single specified taxon attaches to the tree ($|\varphi| = 1$) has marginal density $f_T(x) = 2\lambda e^{-2\lambda x}$.

## Expansion

On the level set $\{\tau(g) = x\}$ the factor $\rho_T(x)/f_T(x)$ is constant, so ratios of $\rho_G$ match ratios of $f_G$, giving (II). Integrating $\rho_G$ over the level set pulls the constant out and leaves $\int \mathbf{1}(\tau(g) = x) f_G(g)\,dg = f_T(x)$, which cancels the denominator and yields $\rho_T(x)$, giving (I); integrating over $x$ then gives total mass $1$. The construction is practical only when $f_T$ can be evaluated: the source derives it for a Yule prior with one calibrated monophyletic clade (where it depends only on the clade size), for one calibration without monophyly as a mixture over how many extra taxa descend from the MRCA, and for some nested calibrations. With several calibrations in general, the induced marginals must be checked by running the MCMC without sequence data.

## Sources

- J. Heled and A. J. Drummond, "Calibrated tree priors for relaxed phylogenetics and divergence time estimation", Systematic Biology 61(1) (2012) 138–149, Eqs. 1–5 and sections "Constructing a Tree Prior with an Arbitrary Marginal Distribution on the Time of an Internal Node" and "Yule Tree Prior with One Calibration Prior, No Monophyly", <https://doi.org/10.1093/sysbio/syr087> (PMC3243734).
