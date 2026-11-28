# Diagonal-Gaussian variational autoencoder

For latent dimension $m\ge1$ and each observation $x$, a probabilistic encoder outputs $\mu_\phi(x)\in\mathbb R^m$ and positive scales $s_\phi(x)\in(0,\infty)^m$. The latent code is sampled as $z=\mu_\phi(x)+s_\phi(x)\odot\epsilon$, with $\epsilon\sim\mathcal N(0,I_m)$. Its law is $q_\phi(z\mid x)=\mathcal N(\mu_\phi(x),\operatorname{diag}(s_\phi(x)^2))$.

With standard normal prior and a decoder likelihood $p_\theta(x\mid z)$ whose expected log is finite, maximize the following per-observation lower bound on $\log p_\theta(x)$:

$$\mathbb E_{\epsilon}\log p_\theta(x\mid\mu+s\odot\epsilon)-\tfrac12\sum_j(\mu_j^2+s_j^2-1-\log s_j^2).$$

The second term subtracts the divergence from the encoder distribution to the prior. The first is a log likelihood, not necessarily squared reconstruction error. The auxiliary noise has a law independent of the encoder parameters.

## Depends on

- [Kullback-Leibler divergence between multivariate Gaussians](../../../InformationTheory/not-yet-classified/part-01/vector-gaussian-kl/kl-div-multivariate-gaussian.md)

## Background

- [Autoencoder reconstruction objective](autoencoder-reconstruction.md)

## Sources

- Kingma and Welling, [*Auto-Encoding Variational Bayes*](https://arxiv.org/abs/1312.6114) (ICLR 2014), §§2.2–3 and appendix B.
