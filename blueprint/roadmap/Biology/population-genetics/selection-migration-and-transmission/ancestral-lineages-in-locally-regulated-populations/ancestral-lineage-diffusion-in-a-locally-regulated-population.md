# Ancestral lineage diffusion in a locally regulated population

**Setting.** Consider the deterministic ($\theta/N\to0$) scaling limit of the locally regulated spatial birth–death process, whose density $(\varphi_t)_{0\le t\le T}$ solves

$$\partial_t\varphi=r\,\mathcal{B}^*(\gamma\varphi)+\varphi F,$$

where $\gamma$ is the fecundity, $r$ the establishment probability, $F$ the scaled net growth (each a function of location and local density), $\mathcal{B}f=\tfrac12\sum_{ij}\mathbf{C}_{ij}\partial_{x_i}\partial_{x_j}f+\sum_i\vec b_i\partial_{x_i}f$ is the generator of offspring dispersal and $\mathcal{B}^*$ its adjoint. Sample an individual at a location $y$ with $\varphi_T(y)>0$, and let $L_s$ be the position of its unique (uniparental) ancestor alive at time $T-s$, $L_0=y$. The lookdown construction gives this lineage a meaning in the infinite-population limit. Let $Q_sf(y)=\mathbb{E}_y[f(L_s)]$.

**Theorem.** For a density $\varphi$ define

$$\mathcal{L}_\varphi f=\frac{r}{\varphi}\Big[\mathcal{B}^*(\gamma\varphi f)-f\,\mathcal{B}^*(\gamma\varphi)\Big]
= r\gamma\Big[\tfrac12\sum_{ij}\mathbf{C}_{ij}\,\partial_{x_i}\partial_{x_j}f+\sum_j m_j\,\partial_{x_j}f\Big],$$

$$m_j=\sum_i\mathbf{C}_{ij}\,\partial_{x_i}\log(\gamma\varphi)+\sum_i\partial_{x_i}\mathbf{C}_{ij}-\vec b_j .$$

Then the (time-inhomogeneous) lineage semigroup satisfies $\partial_sQ_sf(y)=\mathcal{L}_{\varphi_{T-s}}Q_sf(y)$, in a weak sense.

**Isotropic case.** If $\mathbf{C}=\sigma^2 I$ (with $\vec b$ possibly location dependent),

$$\mathcal{L}_\varphi f=\frac{\sigma^2}{2}\,r\gamma\Big(\Delta f+\Big(2\nabla\log(\gamma\varphi)-\frac{2\vec b}{\sigma^2}\Big)\cdot\nabla f\Big).$$

So the lineage is a Brownian motion run at speed $\sigma^2 r\gamma$ (the local rate of producing *established* offspring) and drifts up the gradient of $\log(\gamma\varphi)$ (towards high *juvenile production*) and against the dispersal bias $\vec b$.

## Depends on

- [Scaling limit of a locally regulated spatial birth–death process](scaling-limit-of-a-locally-regulated-spatial-birth-death-process.md)

## Expansion

Run backwards, the lineage jumps from $x$ to $z$ when the individual at $x$ was born to a parent at $z$. Births into $dx$ from parents at $dz$ occur at rate proportional to $\gamma(z)\varphi(z)q_\theta(z,x)r(x)$, so given a lineage at $x$, the parent location has density proportional to $\gamma\varphi(z)q_\theta(z,x)$; normalizing by the total birth flux $\varphi(x)$ and expanding to order $1/\theta$ gives $\frac{r}{\varphi}[\mathcal{B}^*(\gamma\varphi f)-f\mathcal{B}^*(\gamma\varphi)]$. The product rule turns this into the second-order operator with drift $\mathbf{C}\nabla\log(\gamma\varphi)$, plus the Itô correction $\nabla\cdot\mathbf{C}$, minus the forward bias $\vec b$. A naive guess, that a lineage simply reverses dispersal, misses both the fecundity gradient and the speed factor $r\gamma$. In the deterministic limit there is no coalescence; the result describes single-lineage motion, a first step towards genealogies at high density.

## Sources

- Alison M. Etheridge, Thomas G. Kurtz, Ian Letter, Peter L. Ralph and Terence Tsui Ho Lung, "Looking forwards and backwards: Dynamics and genealogies of locally regulated populations", Electron. J. Probab. 29 (2024), 1–85, <https://doi.org/10.1214/24-EJP1075>. Numbering follows the arXiv version, arXiv:2305.14488 (2023): Definition 2.23, Theorem 2.24 and Corollary 2.26 (lookdown construction in Section 5), <https://doi.org/10.48550/arXiv.2305.14488>.
