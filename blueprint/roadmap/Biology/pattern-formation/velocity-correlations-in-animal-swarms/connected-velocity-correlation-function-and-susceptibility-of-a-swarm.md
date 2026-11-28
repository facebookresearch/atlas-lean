# Connected velocity correlation function and susceptibility of a swarm

Let $N$ animals at one instant have positions $\mathbf r_i \in \mathbb R^3$ and velocities
$\mathbf v_i$, and let $\delta\mathbf v_i$ be the velocity fluctuation of animal $i$ after
subtracting the collective modes of the group (translation of the centre of mass, the best-fitting
global rotation and the best-fitting global dilatation). The dimensionless fluctuations are

$$\delta\hat{\boldsymbol\varphi}_i = \frac{\delta\mathbf v_i}
{\sqrt{\frac{1}{N}\sum_{k=1}^{N} \delta\mathbf v_k \cdot \delta\mathbf v_k}} ,$$

so that $\frac1N\sum_i |\delta\hat{\boldsymbol\varphi}_i|^2 = 1$. With $r_{ij} = |\mathbf r_i - \mathbf r_j|$ and a radial binning function $\delta(r - r_{ij})$ equal to $1$ when $r_{ij}$ falls in
the bin of width $dr$ around $r$ and $0$ otherwise, the connected correlation function is

$$C(r) = \frac{\sum_{i \ne j} \delta\hat{\boldsymbol\varphi}_i \cdot \delta\hat{\boldsymbol\varphi}_j\,
\delta(r - r_{ij})}{\sum_{i \ne j}\delta(r - r_{ij})} .$$

The correlation length $\xi$ is the smallest $r$ at which $C(r) = 0$. The cumulative correlation

$$Q(r) = \frac{1}{N}\sum_{i \ne j} \delta\hat{\boldsymbol\varphi}_i \cdot \delta\hat{\boldsymbol\varphi}_j\,
\theta(r - r_{ij}),$$

with $\theta$ the Heaviside function, increases while $C > 0$ and decreases while $C < 0$, so its
first maximum is at $r = \xi$; the susceptibility is $\chi = Q(\xi)$.

## Expansion

Subtracting the collective modes leaves only the part of each velocity that is not explained by
the motion of the group as a whole, so $C(r)$ measures whether neighbours deviate from the group in
the same direction ("connected" correlation). Normalizing by the root-mean-square fluctuation
makes the quantity dimensionless and comparable across swarms and with simulations. Since
$\frac1N\sum_{i,j}\delta\hat{\boldsymbol\varphi}_i\cdot\delta\hat{\boldsymbol\varphi}_j = 0$ once the
mean is subtracted, the correlation must change sign; its first zero sets the range of correlated
behaviour, and the integral of the positive part up to that range combines span and intensity of
correlation. In equilibrium statistical physics this integral equals the response to an external
field. In wild midge swarms, which have no global order, $\xi$ is several times the
nearest-neighbour distance and $\chi$ far exceeds that of non-interacting particles in the same
confinement.

## Sources

- A. Attanasi, A. Cavagna, L. Del Castello, I. Giardina, S. Melillo, L. Parisi, O. Pohl, B. Rossaro,
  E. Shen, E. Silvestri, M. Viale, "Collective behaviour without collective order in wild swarms of
  midges", PLoS Computational Biology 10 (2014) e1003697, Results, Eqs. (1)-(2) and
  "Susceptibility", and Methods, "Velocity fluctuations" (Eqs. 5-7),
  <https://doi.org/10.1371/journal.pcbi.1003697> (PMC4109845).
