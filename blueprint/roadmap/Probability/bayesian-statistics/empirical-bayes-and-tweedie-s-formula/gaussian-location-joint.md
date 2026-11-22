# Joint law of a Gaussian location model

For a prior $g$ on $\mathbb R$ and a variance $v > 0$, the joint law of $(\mu, x)$ in the model $\mu \sim g$, $x \mid \mu \sim \mathcal N(\mu, v)$ is defined as the measure on $\mathbb R \times \mathbb R$ with density $\varphi_v(x - \mu)$ with respect to $g \otimes \text{Lebesgue}$. That it has marginal $g$ and conditional law $\mathcal N(\mu, v)$ is [the joint law of a Gaussian location model has the right marginal and kernel](gaussian-location-joint-prod-apply.md); it is a probability measure when $g$ is one.

## Sources

- Bradley Efron, *Tweedie's formula and selection bias*, J. Amer. Statist. Assoc. 106 (2011), no. 496, 1602–1614, DOI 10.1198/jasa.2011.tm11181. Equation numbers are those of the author's manuscript at https://efron.ckirby.su.domains/papers/2011TweediesFormula.pdf. The model is equation (1.2).
