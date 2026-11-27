# Nonlinear decomposition principle for dynamic compartmental systems

**Compartmental system.** Compartments $i = 1, \dots, n$ hold storages $x_i(t) \ge 0$ and exchange material (energy, nutrients, drug, infected individuals) through nonnegative flow rates $f_{ij}(t, \mathbf{x})$ from $j$ to $i$; index $0$ is the exterior, with external inputs $z_i = f_{i0}$ and outputs $y_j = f_{0j}$. Conservation gives

$$\dot x_i = \sum_{j=0}^n f_{ij}(t, \mathbf{x}) - \sum_{j=0}^n f_{ji}(t, \mathbf{x}), \qquad \mathbf{x}(t_0) = \mathbf{x}_0.$$

**Decomposition.** Split each storage as $x_i = \underline{x}_{i_0} + \sum_{k=1}^n x_{i_k}$, where $x_{i_k}$ is the part of compartment $i$'s content that entered the system from outside through compartment $k$ (the $k$-th *subsystem*), and $\underline{x}_{i_k}$ the part derived from the initial stock of compartment $k$ (the $k$-th *initial subsystem*). Flows are split in proportion to storage composition,

$$f_{i_kj_k}(t, \mathbf{x}) = \frac{x_{j_k}(t)}{x_j(t)}\,f_{ij}(t, \mathbf{x}),$$

and the subsystem $k$ receives the external input $z_k$ only at compartment $k$, while initial subsystem $k$ starts from $x_{k,0}\mathbf{e}_k$. This yields a closed nonlinear system for the $2n^2$ decomposed storages, collected in matrices $X(t) = (x_{i_k})$ and $\underline X(t) = (\underline x_{i_k})$.

**Theorem.**
1. *Well-posedness.* The subflow rates are continuous and continuously differentiable in the decomposed state, so the decomposed system has a unique local solution through every $(t_0, \mathbf{x}_0)$.
2. *Fundamental matrix solutions.* $X(t)$ and $\underline X(t)$ are the unique matrix solutions of the decomposed system, and the solution of the original system is $\mathbf{x}(t) = \underline X(t)\mathbf{1} + X(t)\mathbf{1}$. If all $x_{i,0} > 0$ and all inputs $z_i > 0$, the columns of $X(t)$ and of $\underline X(t)$ are linearly independent, so both matrices are invertible.
3. *Nonlinear decomposition principle.* Fix $\alpha_k, \beta_k \in \{0,1\}$ and re-solve the decomposed system with the reduced data: external input $\alpha_k z_k$ at compartment $k$ and initial stock $\beta_k x_{k,0}\mathbf e_k$, giving subsystem solutions $\mathbf x_k^{\alpha,\beta}(t)$ and $\underline{\mathbf x}_k^{\alpha,\beta}(t)$. Then the subsystems with $\alpha_k = 0$, respectively $\beta_k = 0$, vanish identically, and $\mathbf{x}(t) = \sum_k \big(\alpha_k\mathbf{x}^{\alpha,\beta}_k(t) + \beta_k\underline{\mathbf{x}}^{\alpha,\beta}_k(t)\big)$ solves the original system with external inputs $\sum_k \alpha_k z_k\mathbf{e}_k$ and initial condition $\sum_k \beta_k x_{k,0}\mathbf{e}_k$. The subsystem solutions of the unreduced problem cannot be reused: for $n = 1$, $z_1 = 1$, $f_{01} = x^2$ and $x_0 = 1$, the full solution is $x \equiv 1$ with initial subsystem $e^{-t}$, while the problem without input has solution $1/(1+t)$.

## Proof sketch

Proportional splitting means material in a compartment is well mixed: each tracer fraction leaves in proportion to its share of the storage. Summing the subsystem equations over $k$ recovers the original equations because $\sum_k x_{j_k} = x_j$, which gives the representation through $X\mathbf{1}$ and $\underline X\mathbf{1}$. Applying this to the reduced data, a subsystem with no input and no initial stock stays identically zero, so the remaining subsystems sum to the solution of the original system with the reduced inputs and initial data. The subflows depend on the total storages, which change when data are switched off, so the decomposition has to be recomputed. This plays the role of the superposition principle of linear ODEs for nonlinear compartmental models, and it allows tracing how much of each compartment's content originates from each source, as used in ecological network analysis and in epidemic and pharmacokinetic compartment models.

## Sources

- Huseyin Coskun, "Nonlinear decomposition principle and fundamental matrix solutions for dynamic compartmental systems", *Discrete and Continuous Dynamical Systems - B* 24 (2019), 6553–6605, <https://doi.org/10.3934/dcdsb.2019155>. Preprint version: arXiv:1811.11885 (2018), Section 2.1 (compartmental systems), Section 2.2 (state, flow and domain decomposition, subflow definition and its regularity proposition), Section 2.3 (existence-uniqueness theorem and the fundamental matrix solution theorem), Section 2.4 (nonlinear decomposition principle theorem), <https://doi.org/10.48550/arXiv.1811.11885>.
