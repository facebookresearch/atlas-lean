# Asymmetric two-island frequency process and its moment dual

**Setting.** Two types $\mathbf{x}, \mathbf{y}$ live on two islands $i = 1, 2$ (for example active and dormant individuals). The total mass of each type evolves as a two-type Feller diffusion with immigration: on island $i$, type $\mathbf{x}$ has branching variance $c_i^X$, immigration rate $\beta_i^X \ge 0$, and drift matrix $(B^X_{ij})$ whose off-diagonal entries move mass between islands; similarly for $\mathbf{y}$. Condition the total size of island $i$ to be the constant $z_i > 0$ (culling at a dense set of times). The frequency $R^i_t$ of type $\mathbf{x}$ on island $i$ then solves

$$
dR^i_t = b^i(\mathbf{R}_t)\,dt + \sqrt{\frac{c_i^X}{z_i} R^i_t (1 - R^i_t)^2 + \frac{c_i^Y}{z_i} (R^i_t)^2 (1 - R^i_t)}\; dW^i_t,
$$

with, for island $1$ (island $2$ is symmetric),

$$
b^1(\mathbf{r}) = (B^X_{11} - B^Y_{11}) r_1 (1 - r_1) + \frac{z_2}{z_1}\bigl(B^X_{12} (1 - r_1) r_2 - B^Y_{12} r_1 (1 - r_2)\bigr) - \frac{2}{z_1}(c_1^X - c_1^Y) r_1 (1 - r_1) + \frac{\beta_1^X}{z_1}(1 - r_1) - \frac{\beta_1^Y}{z_1} r_1 .
$$

**Results.**
1. *(Well-posedness.)* The SDE has a unique strong solution staying in $[0,1]^2$, Lipschitz in its initial condition in $L^1$; it is a Feller process with the corresponding second-order generator.
2. *(Culling limit.)* The frequency process of the two-type Feller diffusions with immigration, renormalized to island sizes $\mathbf{z}$ at $n$ equally spaced times per unit time, converges weakly in $\mathbb{D}([0,T], [0,1]^2)$ to $\mathbf{R}$ as $n \to \infty$.
3. *(Moment duality.)* If the transition rates $q^{\mathbf{z}}$ of the associated block-counting chain on $\mathbb{N}_0^2 \cup \{\Delta\}$ are nonnegative, then for all $\mathbf{r} \in [0,1]^2$, $\mathbf{n} \in \mathbb{N}_0^2 \cup \{\Delta\}$ and $t > 0$,

$$
\mathbb{E}\bigl[(R^1_t)^{n_1} (R^2_t)^{n_2}\bigr] = \mathbb{E}\bigl[r_1^{N^1_t}\, r_2^{N^2_t}\bigr],
$$

where $(N^1, N^2)$ counts lineages on each island in a [structured coalescent](../../../coalescent-theory/structured-coalescent/structured-coalescent-for-n-lineages-with-a-gene.md) with migration and coalescence, extended by killing (absorption in the cemetery $\Delta$, read as value $0$) or branching driven by immigration and selection.
4. *(Large islands.)* As $z_1 = z_2 = z \to \infty$, $\mathbb{E}\sup_{t \le T} \|\mathbf{R}^{(z)}_t - \mathbf{R}^{(\infty)}_t\|^p \to 0$ for every $p > 1$, where $\mathbf{R}^{(\infty)}$ solves the deterministic ODE with the $1/z$ terms removed, and $\sqrt{z}(\mathbf{R}^{(z)} - \mathbf{R}^{(\infty)})$ converges weakly in $\mathbb{C}([0,T], \mathbb{R}^2)$ to the unique strong solution of a linear Gaussian SDE (a time-inhomogeneous Ornstein–Uhlenbeck process).

## Depends on

- [Structured coalescent for n lineages with a general migration matrix](../../../coalescent-theory/structured-coalescent/structured-coalescent-for-n-lineages-with-a-gene.md)

## Expansion

Fixing island sizes turns ratio dynamics of branching masses into a Wright–Fisher-type diffusion: Itô's formula on $X/(X + Y)$ gives the asymmetric noise $c^X r(1-r)^2 + c^Y r^2 (1-r)$, which collapses to the Wright–Fisher term $c\,r(1-r)$ when $c^X = c^Y$, and the difference $c^X - c^Y$ appears as an effective selection term. Duality is proved by the generator criterion: $H(\mathbf{n}, \mathbf{r}) = r_1^{n_1} r_2^{n_2}$ satisfies $\mathcal{L}^{\mathbf{z}}_{\mathbf{r}} H = \mathcal{Q}^{\mathbf{z}}_{\mathbf{n}} H$, and nonnegativity of the coefficients is what lets $\mathcal{Q}$ be the generator of a Markov chain. Reading the islands as active and dormant compartments connects the dual to seed-bank coalescents.

## Sources

- María Emilia Caballero, Adrián González Casanova and José Luis Pérez, "Two-type branching processes with immigration, and the structured coalescents", *Journal of Applied Probability* 63 (2026), 32–60, <https://doi.org/10.1017/jpr.2025.29>. Numbering as in the preprint arXiv:2109.07645v2, <https://arxiv.org/abs/2109.07645v2>: Equation (3.1), Propositions 3.1–3.2, Theorems 3.1, 4.1, 5.1 and 5.2.
