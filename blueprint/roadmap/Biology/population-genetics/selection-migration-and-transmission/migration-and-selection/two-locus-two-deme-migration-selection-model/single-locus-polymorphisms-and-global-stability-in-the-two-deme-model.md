# Single-locus polymorphisms and global stability in the two-deme migration–selection model

**Single-locus polymorphisms.** In the two-locus two-deme model with $\alpha_1 > 0 > \alpha_2$,
$\beta_1 > 0 > \beta_2$ and migration rates $m_1, m_2 > 0$, define the scaled migration rates

$$\sigma_k = \frac{m_k}{\alpha_k}, \qquad \tau_k = \frac{m_k}{\beta_k}, \qquad k = 1, 2,$$

so $\sigma_1 > 0 > \sigma_2$ and $\tau_1 > 0 > \tau_2$. When locus $\mathsf{B}$ is fixed (for $B_1$ or
$B_2$), locus $\mathsf{A}$ obeys $\dot p_k = \alpha_k p_k(1 - p_k) + m_k(p_{k^*} - p_k)$, whose
internal equilibrium is

$$\hat p_1 = \tfrac{1}{2}\Bigl(1 - 2\sigma_1 + \sqrt{1 - 4\sigma_1\sigma_2}\Bigr), \qquad
\hat p_2 = \tfrac{1}{2}\Bigl(1 - 2\sigma_2 - \sqrt{1 - 4\sigma_1\sigma_2}\Bigr),$$

and symmetrically $\hat q_k$ with $\tau_k$ in place of $\sigma_k$ when locus $\mathsf{A}$ is fixed.
The polymorphism at locus $\mathsf{A}$ is admissible (lies in $(0,1)^2$) if and only if

$$|\sigma_1 + \sigma_2| < 1,$$

and the one at locus $\mathsf{B}$ if and only if $|\tau_1 + \tau_2| < 1$. Each is then globally
asymptotically stable within its one-locus system.

**Linkage equilibrium.** If recombination is strong enough that $D_1 = D_2 = 0$ may be assumed, the
two loci decouple and the dynamics is the Cartesian product of the two one-locus systems. Then a
globally asymptotically stable equilibrium always exists: it is the fully polymorphic equilibrium
$(\hat p_1, \hat p_2, \hat q_1, \hat q_2)$ if and only if both $|\sigma_1 + \sigma_2| < 1$ and
$|\tau_1 + \tau_2| < 1$; a single-locus polymorphism if exactly one of the two conditions fails; and a
monomorphic equilibrium if both fail.

**Weak migration.** For arbitrary recombination rate $\rho \ge 0$ and sufficiently weak migration,
there is a unique, globally attracting, fully polymorphic equilibrium, at which the linkage
disequilibria within demes are positive.

## Depends on

- [Two-locus two-deme migration–selection model](two-locus-two-deme-migration-selection-dynamics.md)
- [Migration–selection balance on an island](../migration-selection-balance-on-an-island.md)

## Expansion

Dividing the equilibrium conditions by $\alpha_k$ gives $p_k(1 - p_k) + \sigma_k(p_{k^*} - p_k) = 0$,
a pair of quadratics whose admissible root is the one displayed; with one-way migration
($\sigma_2 = 0$) it reduces to the island value $\hat p_1 = 1 - \sigma_1$, $\hat p_2 = 0$. The
condition $|\sigma_1 + \sigma_2| < 1$ says that migration, measured against local selection in the
two demes with opposite signs, is weak enough for both alleles to survive; as it is violated the
polymorphism leaves the state space through a monomorphic equilibrium. Global stability of the
one-locus polymorphism is classical (Eyland, 1971), and the product structure transfers it to the decoupled
two-locus system. The weak-migration result follows by perturbing the migration-free system, which
has the stable equilibrium with $A_1B_1$ fixed in deme 1 and $A_2B_2$ in deme 2; to leading order in
the migration rates, lower recombination yields less reduction of differentiation by migration.

## Sources

- A. Akerman, R. Bürger, "The consequences of gene flow for local adaptation and differentiation: a
  two-locus two-deme model", Journal of Mathematical Biology 68 (2014), Section 3,
  Eqs. (3.1), (3.4), (3.5), (3.7), (3.8), Propositions 3.2 and 3.3,
  <https://doi.org/10.1007/s00285-013-0660-z> (PMC3948587).
