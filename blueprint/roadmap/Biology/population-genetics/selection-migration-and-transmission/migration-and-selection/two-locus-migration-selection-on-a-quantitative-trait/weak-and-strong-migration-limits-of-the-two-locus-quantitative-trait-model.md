# Weak- and strong-migration limits of the two-locus quantitative-trait model

In the haploid two-locus two-deme model with quadratic selection towards optima $\pm P$, symmetric migration rate $m$ and recombination rate $r > 0$:

**Part 1 (weak migration).** If every equilibrium of the uncoupled system ($m = 0$) is hyperbolic, then for sufficiently small $m > 0$ each asymptotically stable equilibrium perturbs to a unique asymptotically stable equilibrium, each unstable internal equilibrium to a unique unstable one, and each unstable boundary equilibrium to at most one equilibrium, which is unstable. When the uncoupled dynamics is gradient-like, every trajectory of the coupled system converges to an equilibrium for small $m$, and global asymptotic stability is inherited.

**Part 2 (strong migration).** With spatially averaged haplotype frequencies $\xi_i = \tfrac12(x_{i,\alpha} + x_{i,\beta})$, averaged fitnesses $\omega_i$ and averaged linkage disequilibrium $\Theta = \xi_1\xi_4 - \xi_2\xi_3$, rescaling $s = \sigma\epsilon$, $r = \rho\epsilon$ with $\epsilon \to 0$ gives the strong-migration limit

$$\dot\xi_i = \xi_i(\omega_i - \bar\omega) - \rho\,\eta_i\,\Theta, \qquad x_{i,\alpha} = x_{i,\beta},$$

a panmictic model with optimum $0$. For sufficiently large $m$, all trajectories converge to a forward-invariant manifold close to $x_{i,\alpha} = x_{i,\beta}$; the monomorphic equilibria $M_2$ and $M_3$ (fixation of $Ab$, $aB$) are the only asymptotically stable equilibria; an unstable internal equilibrium exists, satisfying $\hat p_\beta = 1 - \hat p_\alpha$, $\hat q_\beta = 1 - \hat q_\alpha$, $\hat D_\beta = \hat D_\alpha$; and generically every trajectory converges to an equilibrium.

**Part 3 (symmetric internal equilibria).** For every $m$, the dynamics has at least one internal equilibrium satisfying these symmetry relations, and internal equilibria not satisfying them occur in pairs related by $\tilde p_\gamma = 1 - \hat p_{\gamma^*}$, $\tilde q_\gamma = 1 - \hat q_{\gamma^*}$, $\tilde D_\gamma = \hat D_{\gamma^*}$, with identical stability.

Hence strong gene flow erases all haploid polymorphism, whereas the diploid strong-migration limit can still maintain full polymorphism.

## Depends on

- [Two-locus two-deme model of spatially varying stabilizing selection](two-locus-two-deme-model-of-spatially-varying-stabilizing-selection.md)

## Expansion

Part 1 is regular perturbation of hyperbolic equilibria (Karlin–McGregor), combined with a chain-recurrence argument for convergence. Part 2 applies singular perturbation theory: strong migration homogenizes the demes quickly, after which slow selection and recombination act on the averages, reproducing the single-deme analysis with optimum $0$, where $M_2$ and $M_3$ are bistable. Part 3 uses that the symmetric manifold is invariant and contains no boundary equilibria, so Hofbauer's index theorem for dissipative semiflows forces an internal equilibrium of index $1$ on it; the pairing follows from the model's symmetry under exchanging demes together with alleles.

## Sources

- L. Geroldinger and R. Bürger, "A two-locus model of spatially varying stabilizing or directional selection on a quantitative trait", *Theoretical Population Biology* (2014), Section 4, Section 5, Eqs. (5.1)–(5.6) and Proposition 5.1, and Section 6.2, Proposition 6.1 and Eq. (6.14). <https://doi.org/10.1016/j.tpb.2014.03.002> (PMC4048038)
