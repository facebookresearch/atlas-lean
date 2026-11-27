# Weak recruitment feedback rules out Turing patterns in bulk-surface protein clustering

**Setting.** Consider the nondimensional bulk-surface oligomerization model for membrane-protein clustering in the well-mixed cytosol limit, with oligomers of size at most $N = 2$. Monomers $a_1$ and dimers $a_2$ live on the closed membrane surface $\Gamma = \partial\Omega$ and the cytosolic ligand is replaced, through conservation of the total mass $\mathcal{M}_0$, by a nonlocal functional:

$$
\begin{aligned}
\partial_t a_1 &= \Delta_\Gamma a_1 + \gamma\left\{ \frac{k_0 + k_b a_2}{|\Omega|}\left[\mathcal{M}_0 - \int_\Gamma (a_1 + 2a_2)\, ds\right] - a_1 - 2k_m a_1^2 + 2k_2 a_2 \right\},\\
\partial_t a_2 &= d_2 \Delta_\Gamma a_2 + \gamma\left\{ k_m a_1^2 - k_2 a_2 \right\},
\end{aligned}
$$

where $\gamma > 0$ is the ratio of reaction to surface-diffusion time scales, $d_2 > 0$ the relative dimer diffusivity, $k_0 > 0$ the basal binding rate, $k_b \ge 0$ the rate of dimer-recruited binding (positive feedback), and $k_m, k_2 > 0$ the dimerization and dissociation rates. Let $0 = \eta_0 < \eta_1 \le \eta_2 \le \dots$ be the eigenvalues of $-\Delta_\Gamma$.

**Theorem.** Suppose

$$
0 \le k_b \le \frac{2}{\mathcal{M}_0}\min\left\{ k_0 |\Gamma|,\ \frac{d_2\, \eta_i\, |\Omega|}{\gamma} \right\} \quad \text{for all } i \ge 1 .
$$

Then the system has a unique spatially homogeneous steady state, it is linearly stable to homogeneous perturbations, and no diffusion-driven (Turing) instability occurs: every eigenmode of $\Delta_\Gamma$ is linearly stable.

Consequently, spatial clustering through a Turing mechanism requires a sufficiently strong recruitment feedback $k_b$; numerically, larger $k_b$ produces a single-patch cluster on the sphere.

**Uniqueness for general $N$.** Homogeneous steady states satisfy $a_j^* = C_j (a_1^*)^j$ for explicit $C_j > 0$, and $a_1^*$ is a positive root of a polynomial whose only possibly negative coefficient is $C_N(k_0|\Gamma| N - \mathcal{M}_0 k_b)$; hence the steady state is unique whenever $k_0 |\Gamma| N \ge \mathcal{M}_0 k_b$, in particular without feedback ($k_b = 0$).

## Expansion

For $N = 2$, $a_2^* = k_m (a_1^*)^2/k_2$ and $a_1^*$ is the positive root of a quartic whose coefficients are all nonnegative except the constant term when $k_b \le 2k_0|\Gamma|/\mathcal{M}_0$, so the intermediate value theorem gives exactly one root. The homogeneous Jacobian has characteristic polynomial $\lambda^2 + b\lambda + c$ with $b > 0$ and, under the same bound, $c > 0$, so both eigenvalues have negative real parts. For a perturbation along the $l$-th Laplace–Beltrami eigenfunction with $l \ge 1$, the nonlocal term contributes nothing (the eigenfunction has zero mean), and the mode matrix $\tilde{\mathcal{J}} - \eta_l \mathbf{D}$ has trace negative and determinant

$$
c_l = d_2\eta_l^2 + \gamma\eta_l(d_2 + k_2) + \gamma^2 k_2 + 2\gamma k_m a_1^*\left(2 d_2 \eta_l - \frac{\gamma k_b \mathcal{M}_0}{|\Omega|}\right) + \frac{2\gamma^2 (a_1^*)^2 |\Gamma| k_b k_m}{|\Omega|}\left(1 + \frac{2 a_1^* k_m}{k_2}\right),
$$

which is positive when $k_b \le 2 d_2 \eta_l |\Omega|/(\gamma\mathcal{M}_0)$. A negative trace and a positive determinant for every mode $l$ is exactly the absence of a Turing instability. The bound shows the competing roles of the parameters: slow dimer diffusion ($d_2$ small) or fast reactions ($\gamma$ large) shrink the stable range of the feedback.

## Depends on

- [Bulk-surface oligomerization model with recruitment feedback and its mass conservation](bulk-surface-oligomerization-model-and-mass-conservation.md)
- [Diffusion-driven instability](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Sources

- Lucas M. Stolerman, Michael Getz, Stefan G. Llewellyn Smith, Michael Holst, Padmini Rangamani, "Stability Analysis of a Bulk–Surface Reaction Model for Membrane Protein Clustering", Bulletin of Mathematical Biology 82 (2020), 30, <https://doi.org/10.1007/s11538-020-00703-4>. Published version of arXiv:1908.05214, cited next; locators there refer to the arXiv version.
- L. M. Stolerman, M. Getz, S. G. Llewellyn Smith, M. Holst, "Stability Analysis of a Bulk-Surface Reaction Model for Membrane-Protein Clustering," arXiv 2019. Section 3.1 (homogeneous steady states), Proposition 3.1 (structure of the Jacobian), Theorem 3.1 (no diffusion-driven instability for small $k_b$, case $N = 2$). <https://doi.org/10.48550/arXiv.1908.05214>
