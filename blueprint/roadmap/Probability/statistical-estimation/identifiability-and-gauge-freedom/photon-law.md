# Photon-count law: the product of Poisson laws at the transmitted rates

Let the rays form a finite set $\iota$ and the attenuation cells a finite set $\kappa$. For
nonnegative source intensities $I_{0,j}$, a real $\iota \times \kappa$ matrix $A$ and an attenuation
vector $x \in \mathbb{R}^{\kappa}$, the photon-count law at $x$ is the product measure

$$P_x = \bigotimes_{j \in \iota} \mathrm{Poisson}\bigl(\lambda_j(x)\bigr)$$

on count vectors $N \in \mathbb{N}^{\iota}$, where $\lambda_j(x) = I_{0,j}\, e^{-(Ax)_j}$ is the
[transmitted rate](transmitted-rate.md) of ray $j$. The product form is the model's assumption that
the counts in the different rays are independent, with the Poisson factor of rate $\lambda_j(x)$ for
ray $j$.