# Evidence lower bound with a library-size latent variable

Consider a latent-variable model for a count vector $x \in \mathbb{N}^G$ with observed batch label $s$, latent state $z \in \mathbb{R}^d$ and positive library-size factor $\ell$, with independent priors $p(z) = \mathcal{N}(0, I_d)$ and $p(\ell \mid s) = \mathrm{LogNormal}(\ell_\mu(s), \ell_\sigma^2(s))$, and a likelihood $p(x \mid z, \ell, s)$ (in scVI, the product over genes of the [zero-inflated negative binomial laws](zero-inflated-negative-binomial-likelihood-of-the-scvi-generative-model.md)). Take a mean-field variational family

$$q(z, \ell \mid x, s) = q(z \mid x, s)\, q(\ell \mid x, s), \quad q(z \mid x, s) = \mathcal{N}\big(m(x, s), \mathrm{diag}\, v(x, s)\big), \quad q(\ell \mid x, s) = \mathrm{LogNormal}\big(a(x, s), b(x, s)\big),$$

whose parameters are outputs of encoder networks. Then

$$\log p(x \mid s) \;\ge\; \mathbb{E}_{q}\big[\log p(x \mid z, \ell, s)\big] - D_{\mathrm{KL}}\big(q(z \mid x, s) \,\|\, p(z)\big) - D_{\mathrm{KL}}\big(q(\ell \mid x, s) \,\|\, p(\ell \mid s)\big),$$

and the gap equals $D_{\mathrm{KL}}\big(q(z, \ell \mid x, s) \,\|\, p(z, \ell \mid x, s)\big) \ge 0$. Both divergences are explicit:

$$D_{\mathrm{KL}}\big(\mathcal{N}(m, \mathrm{diag}\, v) \,\|\, \mathcal{N}(0, I_d)\big) = \frac12 \sum_{j=1}^d \big(v_j + m_j^2 - 1 - \log v_j\big),$$

$$D_{\mathrm{KL}}\big(\mathrm{LogNormal}(a, b) \,\|\, \mathrm{LogNormal}(\ell_\mu, \ell_\sigma^2)\big) = \log\frac{\ell_\sigma}{\sqrt{b}} + \frac{b + (a - \ell_\mu)^2}{2 \ell_\sigma^2} - \frac12.$$

Summed over cells, the bound is maximized jointly over decoder and encoder parameters by stochastic gradients on minibatches, with the expectation estimated through the reparameterization $z = m + \sqrt{v} \odot \varepsilon$, $\log \ell = a + \sqrt{b}\, \eta$, $\varepsilon \sim \mathcal{N}(0, I_d)$, $\eta \sim \mathcal{N}(0, 1)$.

## Depends on

- [Zero-inflated negative binomial likelihood of the scVI generative model](zero-inflated-negative-binomial-likelihood-of-the-scvi-generative-model.md)

## Proof sketch

Jensen's inequality applied to $\log p(x \mid s) = \log \mathbb{E}_q[p(x, z, \ell \mid s)/q(z, \ell \mid x, s)]$ gives the bound, and the identity $\log p(x \mid s) - \mathrm{ELBO} = D_{\mathrm{KL}}(q \,\|\, p(\cdot \mid x, s))$ identifies the gap. Because both the prior and the variational family factorize over $z$ and $\ell$, the divergence of the joint splits into the two terms. The Kullback–Leibler divergence is invariant under the bijection $\ell \mapsto \log \ell$, so the log-normal term is the Gaussian divergence between $\mathcal{N}(a, b)$ and $\mathcal{N}(\ell_\mu, \ell_\sigma^2)$. The prior centred on the observed log library size per batch is what lets $\ell$ absorb sequencing-depth variation, so that $z$ is left to encode biological variation; a variant without $\ell$ performed worse at clustering and differential expression.

## Sources

- R. Lopez, J. Regier, M. B. Cole, M. I. Jordan and N. Yosef, "Deep generative modeling for single-cell transcriptomics", Nature Methods 15 (2018), 1053–1058, Online Methods (section "Fast inference via stochastic optimization", Equation 2), <https://doi.org/10.1038/s41592-018-0229-2>, PMCID: PMC6289068.
