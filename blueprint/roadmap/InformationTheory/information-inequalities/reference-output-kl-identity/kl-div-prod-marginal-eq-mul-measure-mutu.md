# Kl Div prod marginal eq mul measure Mutual Information

Let $X$ and $Y$ be measurable spaces and let $\mu$ be a probability measure on $X \times Y$ with marginals $\mu_X$ and $\mu_Y$. Write $I(\mu) = D_{\mathrm{KL}}(\mu \parallel \mu_X \otimes \mu_Y) / \ln 2 \in [0, \infty]$ for its mutual information in bits. Taking the reference equal to the actual output marginal, the reference divergence is the mutual information in nats:

$$D_{\mathrm{KL}}(\mu \parallel \mu_X \otimes \mu_Y) = \ln 2 \cdot I(\mu).$$
