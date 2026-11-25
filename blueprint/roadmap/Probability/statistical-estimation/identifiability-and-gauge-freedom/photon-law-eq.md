# The photon-count law is the product of the rays' Poisson laws

For finite sets of rays and attenuation cells, nonnegative source intensities $I_{0,j}$, a real
matrix $A$ indexed by rays and cells and an attenuation vector $x$, the
[photon-count law](photon-law.md) at $x$ is

$$P_x = \bigotimes_{j} \mathrm{Poisson}\bigl(\lambda_j(x)\bigr),$$

the product over the rays $j$ of the Poisson laws whose means are the
[transmitted rates](transmitted-rate.md) $\lambda_j(x) = I_{0,j}\, e^{-(Ax)_j}$. This is the
definition unfolded.
