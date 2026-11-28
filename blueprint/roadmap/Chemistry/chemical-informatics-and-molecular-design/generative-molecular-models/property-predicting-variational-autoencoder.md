# Property-predicting variational autoencoder for molecules

Training a variational autoencoder on molecular strings together with a property predictor on its latent code is the design proposal that made molecular search continuous. The objective below is one specialization of that proposal, written out so that each of its terms is defined.

Let molecules be strings $x$ over a finite alphabet, so that a decoder $p_{\theta}(x \mid z)$ is a probability mass function on strings for each $z \in \mathbb{R}^{d}$. Let the prior $p(z)$ and the encoder $q_{\phi}(z \mid x)$ be probability densities on $\mathbb{R}^{d}$ with respect to Lebesgue measure, with $q_{\phi}(\cdot \mid x)$ absolutely continuous with respect to $p$ and having finite mean $\mu_{\phi}(x) \in \mathbb{R}^{d}$, and let $f_{\psi} \colon \mathbb{R}^{d} \to \mathbb{R}^{p}$ predict $p$ target properties. The evidence lower bound at $x$ is the integral

$$
\mathcal{L}(\theta, \phi; x) = \int_{\mathbb{R}^{d}} q_{\phi}(z \mid x) \log p_{\theta}(x \mid z)\, \mathrm{d}z \; - \; \int_{\mathbb{R}^{d}} q_{\phi}(z \mid x) \log \frac{q_{\phi}(z \mid x)}{p(z)}\, \mathrm{d}z ,
$$

assumed to exist and be finite. With a training distribution $\mathcal{D}$ over labelled molecules $(x,y)$ and a weight $\gamma > 0$, the joint objective of this page is

$$
\min_{\theta, \phi, \psi} \; \mathbb{E}_{(x,y) \sim \mathcal{D}}\Big[ -\mathcal{L}(\theta, \phi; x) + \gamma \, \big\| f_{\psi}(\mu_{\phi}(x)) - y \big\|^{2} \Big] ,
$$

assumed integrable over $\mathcal{D}$.

Scope. The source trains encoder, decoder and predictor jointly, with the variational term annealed, and reports latent-space design by fitting a separate Gaussian-process surrogate on encoded training molecules and optimizing that surrogate; the constant weight, the squared loss and its evaluation at the encoder mean are this page's specialization, not a formula the source prints. Nothing here implies that a neighbourhood of a code decodes to related molecules, which is an empirical property of a trained model, and with an unconstrained string representation decoded strings need not parse at all, which the source handles by a validity filter. A deterministic encoder is not a boundary case of the display: a point mass against an atomless prior is not absolutely continuous and the second integral is not finite, so dropping the variational setup gives a different model, an autoencoder with a regression head, rather than a limit of this one. Setting $\gamma = 0$ does leave the plain variational objective.

The bound is written out above because it is the continuous-latent one, over a latent space with a base measure, rather than the finite-latent bound of a discrete model.

## Depends on

None.

## Proof depends on

None.

## Expansion

A canonical continuous-latent evidence lower bound, together with the encoder, decoder and reparameterization, is the prerequisite this construction takes once it is available. A formal development fixes the latent dimension, the measures and densities named above, defines $\mathcal{L}$ by the displayed integrals with their finiteness hypotheses, and defines the objective as the $\mathcal{D}$-expectation of the displayed integrand. Worth recording are the hypotheses that make each term meaningful: absolute continuity of the encoder with respect to the prior for the second integral, finiteness of the encoder mean for the regression term, and integrability over $\mathcal{D}$ for the objective. The surrogate-based design loop of the source is a separate object and belongs on its own page if it is stated.

## Context

Graduate. The model of Gómez-Bombarelli, Wei, Duvenaud, Hernández-Lobato, Sánchez-Lengeling, Sheberla, Aguilera-Iparraguirre, Hirzel, Adams and Aspuru-Guzik that opened continuous-space inverse design; the validity problem it filters around is what the SELFIES chapter of this roadmap addresses at the representation level.

## Sources

- Rafael Gómez-Bombarelli, Jennifer N. Wei, David Duvenaud, José Miguel Hernández-Lobato, Benjamín Sánchez-Lengeling, Dennis Sheberla, Jorge Aguilera-Iparraguirre, Timothy D. Hirzel, Ryan P. Adams and Alán Aspuru-Guzik, *Automatic Chemical Design Using a Data-Driven Continuous Representation of Molecules*, ACS Central Science 4 (2018) 268–276, Figure 1, the property-prediction section and the section on optimization of molecules via properties, which fits a separate Gaussian-process surrogate. DOI [10.1021/acscentsci.7b00572](https://doi.org/10.1021/acscentsci.7b00572), arXiv:[1610.02415v3](https://arxiv.org/abs/1610.02415v3).
- Diederik P. Kingma and Max Welling, *Auto-Encoding Variational Bayes*, International Conference on Learning Representations 2014, Section 2.2, for the continuous variational lower bound written above. arXiv:[1312.6114v11](https://arxiv.org/abs/1312.6114v11).
