# p-adic reaction-diffusion model of coral calcification

**Hierarchical space.** Branch positions of a coral colony are encoded by $x \in \mathbb{Z}_p$, the $p$-adic integers, whose balls form a $p$-ary tree; two branches are closer in the ultrametric $|x - y|_p$ the more bifurcation levels they share. Diffusion across the hierarchy is modeled by the Vladimirov operator, a $p$-adic analog of the fractional Laplacian: for $\alpha > 0$,

$$ \boldsymbol{D}^\alpha u(x) = \frac{1 - p^{\alpha}}{1 - p^{-\alpha-1}} \int_{\mathbb{Q}_p} \frac{u(y) - u(x)}{|x - y|_p^{1+\alpha}}\, dy, $$

restricted (as $\overline{\boldsymbol{D}}^\alpha$) to locally constant functions supported in $\mathbb{Z}_p$.

**Chemistry.** With the reactions $\mathrm{CO_2 + H_2O + CO_3^{2-}} \to 2\,\mathrm{HCO_3^-}$ (rate $k_1$) and $\mathrm{Ca^{2+} + 2\,HCO_3^-} \to \mathrm{CaCO_3 + H_2O + CO_2}$ (rate $k_2$), mass-action kinetics for carbonate $u$, calcium $v$ and calcium carbonate $w$, together with the conservation identities $[\mathrm{CO_2}] = z_0 - s$ and $s = v - u + u_0 - v_0$ for bicarbonate $s$ (no initial products), reduce the system to three species. Letting only carbonate and calcium diffuse and nondimensionalizing gives

$$ \partial_t u = -\overline{\boldsymbol{D}}^\alpha u - u (u - v + \sigma - \beta), \qquad \partial_t v = -d\, \overline{\boldsymbol{D}}^\alpha v - \eta v (v - u + \beta)^2, \qquad \partial_t w = \eta v (v - u + \beta)^2, $$

with $d = d_2/d_1$ the ratio of diffusion coefficients, $\eta = d_1 k_2 / (k_1')^2$, $\beta = (u_0 - v_0) k_1'/d_1 < 0$ (calcium exceeds carbonate in seawater) and $\sigma = z_0 k_1'/d_1$ encoding the dissolved $\mathrm{CO_2}$ level, where $k_1' = k_1 [\mathrm{H_2O}]$.

**Discretization and well-posedness.** Partitioning $\mathbb{Z}_p$ into the $p^m$ balls of radius $p^{-m}$ (one per terminal branch, indexed by $G_m$), the Vladimirov operator becomes the matrix $L^\alpha$ acting by

$$ (L^\alpha \mathbf{u})_i \propto \sum_{j \in G_m,\ j \ne i} \frac{p^{-m} (u_j - u_i)}{|i - j|_p^{\alpha + 1}}, $$

and the model becomes the ODE system $\dot{\mathbf u} = L^\alpha \mathbf u + F$, $\dot{\mathbf v} = L^\alpha \mathbf v + G$, $\dot{\mathbf w} = H$ with polynomial reaction terms. For any initial data it has a unique local solution $(\mathbf u, \mathbf v, \mathbf w) \in C^1((t_0 - \delta, t_0 + \delta), \mathbb{R}^{3 p^m})$ (appendix proposition). Numerically, varying $\sigma$ (the $\mathrm{CO_2}$ concentration) and the kinetic parameters changes the spatial distribution of deposited $\mathrm{CaCO_3}$ across branches and produces diverse branching calcification patterns.

## Expansion

Because functions are locally constant on balls of radius $p^{-m}$, the Vladimirov integral reduces exactly to a finite weighted sum over the other balls, with weights depending only on the ultrametric distance between ball centers, plus a constant diagonal correction from the restriction to $\mathbb{Z}_p$; the kernel couples every pair of branches, with strength decaying with the level at which they separate. The reaction terms are polynomial, hence locally Lipschitz, so local existence and uniqueness follow from the Picard-Lindelöf theorem. The hierarchical (tree) geometry is thus built into the diffusion operator rather than into a Euclidean domain, which is what lets the model represent nonlocal ion exchange across a ramified colony.

## Sources

- Angela Fuquen-Tibatá, Yuriria Cortés-Poza, J. Rogelio Pérez-Buendía, "A p-adic reaction-diffusion model of branching coral growth and calcification dynamics", Journal of Mathematical Biology 92 (2026), 27, <https://doi.org/10.1007/s00285-025-02340-8>. Published version of arXiv:2512.00755, cited next; locators there refer to the arXiv version.
- Angela Fuquen-Tibatá, Yuriria Cortés-Poza, J. Rogelio Pérez-Buendía, "A $p$-adic Reaction--Diffusion Model of Branching Coral Growth and Calcification Dynamics", arXiv (2025). Section 2 (Vladimirov operator), Section 3 (biochemical $p$-adic model and nondimensionalization), Section 4 (discretization), appendix proposition on local well-posedness. <https://doi.org/10.48550/arXiv.2512.00755>
