# Pairwise coalescence density under two-dimensional diffusion of ancestry

Consider two homologous loci sampled at geographic distance $r \ge 0$ in a population spread over the plane $\mathbb{R}^2$. Back in time, each ancestral lineage moves as an independent planar Brownian motion whose displacement after $t > 0$ generations is Gaussian $N(0, \sigma^2 t)$ along each axis, where $\sigma > 0$ is the dispersal rate (the root mean squared axial parent–offspring distance when single-generation displacements are uncorrelated). Then the difference of the two lineage positions after $t$ generations has the planar Gaussian density with variance $2\sigma^2 t$ per axis, and its density at the origin is

$$p(0, t) = \frac{1}{4\pi \sigma^2 t} \exp\left(-\frac{r^2}{4 \sigma^2 t}\right).$$

Assume lineages that are close together coalesce at a local rate $1/(2 D_e(t))$, where $D_e(t) > 0$ is the effective density at time $t$ in the past (defined through the integral of the local coalescence kernel, so that $D_e$ is the number of diploid individuals per unit area in a stepping-stone limit). To first order in the coalescence rate, that is, for recent times at which the probability of an earlier coalescence can be neglected, the rate (intensity) at which the two loci coalesce at time $t$ is

$$\psi(t) = \frac{1}{2 D_e(t)} \cdot \frac{1}{4\pi \sigma^2 t} \exp\left(-\frac{r^2}{4 \sigma^2 t}\right), \qquad t > 0.$$

This $\psi$ is a first-order intensity, not the probability density of the time to the most recent common ancestor on the whole time axis: for constant $D_e$ and $r > 0$, $\psi(t) \sim t^{-1}/(8\pi D_e \sigma^2)$ as $t \to \infty$, so $\int_0^\infty \psi(t)\, dt = \infty$. Integrals of $\psi$ against factors that decay in $t$ (such as $e^{-2\mu t}$ or $e^{-2Lt}$) give first-order approximations to probabilities and expected counts.

## Proof sketch

The two lineages move independently, so their difference is Gaussian with the sum of the two covariance matrices, $2\sigma^2 t I_2$, and mean equal to the initial separation; evaluating the planar Gaussian density at the origin gives $p(0,t)$. The local coalescence rate multiplies the probability density of being at distance zero: writing $\psi(t) = \int_{\mathbb{R}^2} p(x, t) \nu(x)\, dx$ for a coalescence kernel $\nu$ concentrated near the origin, and replacing $p(x,t)$ by $p(0,t)$ on the support of $\nu$, gives $\psi(t) \approx p(0,t) \int \nu = p(0,t)/(2D_e)$. The approximation ignores that coalesced lineages stay together (it does not discount the probability that coalescence already happened), which is accurate for well-separated samples and recent times and is why the total mass of $\psi$ need not be at most one.

## Proof depends on

- [Convolution powers of a Gaussian are Gaussian](../../../../Probability/infinite-divisibility-regular-variation/stable-distributions-and-domains-of-attraction/conv-pow-gaussian-real.md)

## Sources

- H. Ringbauer, G. Coop and N. H. Barton, Inferring recent demography from isolation by distance of long shared sequence blocks, *Genetics* 205 (2017), 1335–1351, <https://doi.org/10.1534/genetics.116.196220>, PMCID PMC5340342 (Equations 1 and 6; Appendix A, Equation A1).
