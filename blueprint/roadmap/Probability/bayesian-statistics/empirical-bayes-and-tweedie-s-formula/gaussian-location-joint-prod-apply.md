# The joint law of a Gaussian location model has the right marginal and kernel

For an s-finite prior $g$, $v > 0$ and measurable sets $A, B \subseteq \mathbb R$, the [joint law](gaussian-location-joint.md) satisfies

$$\mathbb P(\mu \in A,\ x \in B) = \int_A \mathcal N(\mu, v)(B)\, g(d\mu) .$$

Rectangles determine the measure, so this identifies the joint law with the composition of $g$ and the Gaussian kernel $\mu \mapsto \mathcal N(\mu, v)$, which is model (1.2) of Efron (2011).

## Sources

- Bradley Efron, *Tweedie's formula and selection bias*, J. Amer. Statist. Assoc. 106 (2011), no. 496, 1602–1614, DOI 10.1198/jasa.2011.tm11181. Equation numbers are those of the author's manuscript at https://efron.ckirby.su.domains/papers/2011TweediesFormula.pdf.
