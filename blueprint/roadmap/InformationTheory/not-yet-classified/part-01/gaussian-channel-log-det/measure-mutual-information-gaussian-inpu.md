# Log-det formula for the joint law of a Gaussian channel

Let $\iota, \kappa$ be finite index sets with $\iota$ nonempty, $H$ a real $\iota \times \kappa$ matrix, $K$ positive semidefinite (possibly singular) and $R$ positive definite. Let $\mu$ be the joint law of input and output when the input has law $\mathcal{N}(0, K)$ and the channel sends $x$ to the law of $Hx + Z$, $Z \sim \mathcal{N}(0, R)$. The mutual information of $\mu$, in bits, is $I(\mu) = D_{\mathrm{KL}}(\mu \,\|\, \mu_X \otimes \mu_Y)/\ln 2$ with $\mu_X, \mu_Y$ the marginals, and

$$I(\mu) = \frac{1}{2 \ln 2}\, \ln \frac{\det(R + H K H^\top)}{\det R}.$$
