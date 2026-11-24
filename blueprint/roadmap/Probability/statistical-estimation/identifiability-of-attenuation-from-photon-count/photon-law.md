# Photon-count law: the product of Poisson laws at the transmitted rates

Let the rays form a finite set $\iota$ and the attenuation cells a finite set $\kappa$. For
nonnegative source intensities $I_{0,j}$, a real $\iota \times \kappa$ matrix $A$ and an attenuation
vector $x \in \mathbb{R}^{\kappa}$, the photon-count law at $x$ is the product measure

$$P_x = \bigotimes_{j \in \iota} \mathrm{Poisson}\bigl(\lambda_j(x)\bigr)$$

on count vectors $N \in \mathbb{N}^{\iota}$, where $\lambda_j(x) = I_{0,j}\, e^{-(Ax)_j}$ is the
[transmitted rate](transmitted-rate.md) of ray $j$. In the model it describes independent counts in
the different rays, the count of ray $j$ being Poisson with rate $\lambda_j(x)$; the independence is
an assumption of the model, built into the product.
