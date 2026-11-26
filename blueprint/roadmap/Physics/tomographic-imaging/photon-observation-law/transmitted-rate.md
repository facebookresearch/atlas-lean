# Transmitted Poisson rate of a ray

For rays $j \in \iota$ and a finite set of cells $\kappa$, take nonnegative source intensities $I_0(j)$, an arbitrary real design matrix $A \in \mathbb{R}^{\iota \times \kappa}$ (in applications, $A_{jk}$ is the intersection length of ray $j$ with cell $k$) and attenuation coefficients $x \in \mathbb{R}^{\kappa}$. The transmitted rate of ray $j$ is the nonnegative real number

$$I_0(j)\, e^{-(A x)_j}.$$

This is the monochromatic Beer–Lambert model: a single energy, so one attenuation coefficient per cell and an exponential decay along the ray. For a mixture of energies, the negative log of the transmitted fraction need not equal the mean attenuation (see [the two-energy mixture counterexample](../monochromatic-ct-attenuation/mixture-log-ne-mean.md)).
