# Moments of first-passage times as spanning-forest ratios

**Setting.** As for splitting probabilities: $G$ is a linear-framework graph whose terminal strongly
connected components are single vertices, forming the set $Z$; $w$, $\Phi_A(G)$ and $\Phi_{B\to A}(G)$
denote forest weights and rooted spanning-forest sets; $z \in Z$, and $U$ satisfies
$Z \subseteq U \subseteq \overline{V^-_{\mathrm{in}}(z)}$.

**Theorem 5 (conditional first-passage time).** For $i \in V^-_{\mathrm{in}}(z)$, the $r$-th moment of
the first-passage time from $i$ to $z$, conditioned on absorption at $z$, is

$$\mu^{(r)}_{c,i,z} = r! \sum_{(i_1,\dots,i_r) \in \bar U^{\,r}} \left(\prod_{j=0}^{r-1}\frac{w\big(\Phi_{U\cup\{i_j\}\to U\cup\{i_{j+1}\}}(G)\big)}{w\big(\Phi_U(G)\big)}\right)\frac{w\big(\Phi_{(U\setminus\{z\})\cup\{i_r\}\to U}(G)\big)}{w\big(\Phi_{(U\setminus\{z\})\cup\{i\}\to U}(G)\big)}, \qquad i_0 = i.$$

In particular the conditional mean is

$$\mu^{(1)}_{c,i,z} = \sum_{j \in \bar U} \frac{w\big(\Phi_{U\cup\{i\}\to U\cup\{j\}}(G)\big)}{w\big(\Phi_U(G)\big)}\cdot\frac{w\big(\Phi_{(U\setminus\{z\})\cup\{j\}\to U}(G)\big)}{w\big(\Phi_{(U\setminus\{z\})\cup\{i\}\to U}(G)\big)}.$$

**Theorem 6 (unconditional absorption time).** For $i \notin Z$, the $r$-th moment of the time to reach
$Z$ is

$$\mu^{(r)}_{i,Z} = r! \sum_{(i_1,\dots,i_r)\in \bar Z^{\,r}} \prod_{j=0}^{r-1}\frac{w\big(\Phi_{Z\cup\{i_j\}\to Z\cup\{i_{j+1}\}}(G)\big)}{w\big(\Phi_Z(G)\big)}, \qquad i_0 = i,$$

with mean $\mu^{(1)}_{i,Z} = \sum_{j\in\bar Z} w(\Phi_{Z\cup\{i\}\to Z\cup\{j\}}(G))/w(\Phi_Z(G))$.

**Proposition 7 (one terminal vertex).** If $z$ is the only terminal vertex, the $r$-th moment of the
first-passage time from $i$ to $z$ is
$r!\sum_{(i_1,\dots,i_r)\in (V(G)\setminus\{z\})^r}\prod_{j=0}^{r-1} w(\Phi_{\{i_j,z\}\to\{i_{j+1},z\}}(G))/w(\Phi_{\{z\}}(G))$,
with mean $\sum_{j\ne z} w(\Phi_{\{i,z\}\to\{j,z\}}(G))/w(\Phi_{\{z\}}(G))$.

All these are manifestly positive rational functions of the transition rates with units of
$\text{time}^r$.

## Depends on

- [Splitting probabilities as spanning-forest ratios](splitting-probabilities-as-spanning-forest-ratios.md)

## Proof depends on

- [Spanning-forest formula for inverses of Laplacian submatrices](spanning-forest-formula-for-inverses-of-laplacian-submatrices.md)

## Expansion

With $M = \mathcal L[V^-_{\mathrm{in}}(z), V^-_{\mathrm{in}}(z)]$ and $\mathcal L = -L(G)^{\mathsf T}$,
differentiating the Laplace transform $(sI + M)^{-1}v$ at $s = 0$ gives the unnormalized moments
$\mu^{(r)}_z = r!\, M^{-(r+1)} v = r!\, M^{-r}\pi_z$; dividing by $\pi_{i,z}$ conditions on absorption at
$z$. Expanding the matrix power entrywise and substituting the spanning-forest formula for $M^{-1}$
gives the $r$-fold product, and the ratio $\pi_{i_r,z}/\pi_{i,z}$ is replaced using the splitting
formula; tuples through vertices that cannot reach $z$ contribute zero, which allows summing over all
of $\bar U^{\,r}$. For Theorem 6, summing the conditional moments weighted by $\pi_{i,z}$ over $z$ uses
$\sum_{z} \pi_{i_r,z} = 1$. Each ratio in the product has one fewer edge label in the numerator than in
the denominator, which is how the units of time appear.

## Sources

- K.-M. Nam, J. Gunawardena, "Algebraic formulas for first-passage times of Markov processes in the linear framework", Bulletin of Mathematical Biology 87(11) (2025) 161, <https://doi.org/10.1007/s11538-025-01524-z> (PMC12521310). Theorem 5, Eq. (52), Eq. (53), Theorem 6, Eq. (55), Proposition 7, Eq. (57), Eqs. (43)–(51).
