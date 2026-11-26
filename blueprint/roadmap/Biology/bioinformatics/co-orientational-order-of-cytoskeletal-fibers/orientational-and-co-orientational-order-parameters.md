# Orientational and co-orientational order parameters

**Orientational order parameter.** Let $K$ be a family of fiber orientations in the plane, given as unit pseudo-vectors $\vec k_i = (\cos\varphi_i, \sin\varphi_i)$, $i = 1, \dots, n$, defined only up to sign (orientation angles modulo $\pi$). The *mean order tensor* and *orientational order parameter* (OOP) are

$$\mathbb T_K = \Big\langle 2\, \vec k_i \vec k_i^{\mathsf T} \Big\rangle - \mathbb I = \begin{pmatrix} \langle \cos 2\varphi_i\rangle & \langle \sin 2\varphi_i \rangle \\ \langle \sin 2\varphi_i \rangle & -\langle \cos 2\varphi_i \rangle \end{pmatrix}, \qquad \mathrm{OOP}_K = \lambda_{\max}(\mathbb T_K) = \sqrt{\langle \cos 2\varphi_i\rangle^2 + \langle \sin 2\varphi_i\rangle^2},$$

where $\langle \cdot \rangle$ is the average over $i$. $\mathrm{OOP}_K \in [0, 1]$, equal to $1$ for perfectly aligned fibers and near $0$ for isotropic ones; the eigenvector of $\lambda_{\max}$ is the *director* (mean orientation).

**Co-orientational order parameter.** Let $P = \{\vec p_i\}$ and $Q = \{\vec q_i\}$ be two families of unit pseudo-vectors co-localized at the same $n$ sites (for example actin fibers and Z-lines in the same cell). Form the field $F$ of relative orientations

$$f_{i,x} = \vec p_i \cdot \vec q_i = \cos\theta_i, \qquad f_{i,y} = p_{i,x} q_{i,y} - p_{i,y} q_{i,x} = \sin\theta_i,$$

where $\theta_i$ is the angle between $\vec p_i$ and $\vec q_i$. Then

$$\mathbb T_{PQ} = \Big\langle 2\, \vec f_i \vec f_i^{\mathsf T} \Big\rangle - \mathbb I, \qquad \mathrm{COOP}_{PQ} = \lambda_{\max}(\mathbb T_{PQ}) = \langle f_{i,x}^2\rangle + \langle f_{i,y}^2 \rangle - 1 + \sqrt{\big(\langle f_{i,x}^2\rangle - \langle f_{i,y}^2\rangle\big)^2 + 4 \langle f_{i,x} f_{i,y}\rangle^2},$$

equivalently $\mathrm{COOP}_{PQ} = \langle 2 (\vec f_i \cdot \hat n)^2 \rangle - 1$ with $\hat n$ the director of $\mathbb T_{PQ}$ (the mean relative angle).

**Properties.** (1) *Symmetry*: $\mathrm{COOP}$ is unchanged by flipping the sign of any $\vec p_i$ or $\vec q_i$ and by swapping $P$ and $Q$. (2) *Rotation invariance*: rotating every $\vec q_i$ by a fixed angle leaves $\mathrm{COOP}$ unchanged, so the mean angle between families carries no information about correlation and one may take both directors along $(1, 0)$. (3) *Normalization*: $\mathrm{COOP}_{PP} = 1$, and $\mathrm{COOP} \in [0, 1]$.

## Expansion

For unit vectors $2\vec k\vec k^{\mathsf T} - \mathbb I$ is the reflection-type matrix with entries $\cos 2\varphi$, $\sin 2\varphi$, trace zero, so the mean tensor is symmetric traceless with eigenvalues $\pm\sqrt{\langle\cos 2\varphi\rangle^2 + \langle \sin 2\varphi\rangle^2}$; since $\vec k \mapsto -\vec k$ leaves $\vec k\vec k^{\mathsf T}$ fixed, the tensor respects the $\pi$-periodicity of pseudo-vectors. The same computation applied to $\vec f_i$ gives the closed form (the general $2\times 2$ symmetric eigenvalue formula reduces to the radical shown). Flipping $\vec p_i$ or $\vec q_i$ flips $\vec f_i$, which leaves $\vec f_i \vec f_i^{\mathsf T}$ fixed; swapping $P$ and $Q$ conjugates $\theta_i \mapsto -\theta_i$, a reflection, which preserves eigenvalues. A common rotation of $Q$ by $\nu$ shifts every $\theta_i$ by $\nu$, rotating $\mathbb T_{PQ}$ by $2\nu$, which preserves eigenvalues. If $Q = P$ then every $\theta_i = 0$, $\vec f_i = (1, 0)$, $\mathbb T_{PQ} = \operatorname{diag}(1, -1)$ and $\mathrm{COOP} = 1$.

## Sources

- N. K. Drew, M. A. Eagleson, D. B. Baldo, K. K. Parker, A. Grosberg, "Metrics for assessing cytoskeletal orientational correlations and consistency", *PLoS Computational Biology* 11(4) (2015) e1004190. Methods/Results: OOP, Eqs. (1)–(2); COOP, Eqs. (3)–(8); Theorem 1 (symmetry), Theorem 2 (field rotation), Theorem 3 (same field gives 1). <https://doi.org/10.1371/journal.pcbi.1004190>. PMCID: PMC4388480.
