# Expected plant and seed numbers in a grouped dispersal process

**Model.** A two-type measure-valued process describes plants (located at points $x$) and moving seeds (pairs $(x,y)$ of mother-plant location and current position). Each plant releases, at unit rate, a group of $\kappa$ seeds with probability $q(\kappa)$, all placed at one point $y$ drawn from a displacement kernel $D(x,\cdot)$ (a probability density); seeds then diffuse, and a seed matures into a plant at rate $\lambda(x,y)$. Plants do not die. Let $N_p(t)$ and $N_s(t)$ be the numbers of plants and seeds, and $\mu = \sum_\kappa q(\kappa)\kappa$ the mean group size.

**Theorem.** If $\lambda\equiv 1$ and the process starts from a single plant and no seeds, then

$$\mathbb{E}N_p(t) = \frac{(\sqrt{4\mu+1}-1)\,e^{\frac12(\sqrt{4\mu+1}-1)t} + (\sqrt{4\mu+1}+1)\,e^{-\frac12(\sqrt{4\mu+1}+1)t}}{2\sqrt{4\mu+1}},$$

$$\mathbb{E}N_s(t) = \frac{\mu\big(e^{\frac12(\sqrt{4\mu+1}-1)t} - e^{-\frac12(\sqrt{4\mu+1}+1)t}\big)}{\sqrt{4\mu+1}}.$$

In particular the population grows exponentially at rate $\frac12(\sqrt{4\mu+1}-1)$. Under a large-population rescaling with $\sup_K\mathbb{E}[\langle1,\nu_p^{(K)}(0)\rangle^3+\langle1,\nu_s^{(K)}(0)\rangle^3]<\infty$, the rescaled process converges in law on $[0,T]$ to deterministic densities $f(t,x)$ (plants) and $g(t,x,y)$ (seeds) solving $\partial_t f(t,x) = \int\lambda(z,x)g(t,z,x)\,dz$ and $\partial_t g = L^{*}g - \lambda g + \mu D(x,y)f(t,x)$, where $L^{*}$ is the adjoint of the seed-motion generator acting in $y$ (with a no-flux condition in $y$ on the boundary).

## Expansion

Applying the generator to $\langle 1,\nu_p\rangle$ and $\langle 1,\nu_s\rangle$ gives the closed linear system $\frac{d}{dt}\mathbb{E}N_p = \mathbb{E}N_s$ and $\frac{d}{dt}\mathbb{E}N_s = \mu\,\mathbb{E}N_p - \mathbb{E}N_s$, since maturation moves one seed to the plant class and each release adds $\kappa$ seeds on average $\mu$. Its eigenvalues are the roots $\frac12(-1\pm\sqrt{4\mu+1})$ of $s^2+s-\mu=0$, and the initial condition $(1,0)$ fixes the coefficients.

## Sources

- M. Ayala, J. Coville, S. Soubeyrand, "Group dispersal modelling revisited", arXiv:2405.08384, Section 1 (generator), Theorem 1.2 and Proposition 2.1. <https://doi.org/10.48550/arXiv.2405.08384>
