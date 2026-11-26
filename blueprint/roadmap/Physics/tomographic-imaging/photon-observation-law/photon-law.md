# Photon count law of a CT design

For rays $j \in \iota$ and cells $\kappa$, both finite, take nonnegative source intensities $I_0(j)$, a real design matrix $A \in \mathbb{R}^{\iota \times \kappa}$ and attenuation coefficients $x \in \mathbb{R}^{\kappa}$. The photon law at $x$ is the probability distribution on count vectors $n \in \mathbb{N}^{\iota}$ under which the counts of the rays are independent and the count of ray $j$ is Poisson with mean the [transmitted rate](transmitted-rate.md) $I_0(j)\, e^{-(A x)_j}$ of the monochromatic Beer–Lambert model.
