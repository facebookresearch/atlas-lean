# Two-locus two-deme model of spatially varying stabilizing selection

A sexual population occupies two demes $\alpha, \beta$. In deme $\gamma$ the Malthusian fitness of genotypic value $G$ is

$$w_\gamma(G) = w_0 - s(G - P_\gamma)^2, \qquad s > 0,$$

with symmetric optima $P_\beta = -P_\alpha = P \in [0,1]$ and symmetric migration rate $m_\alpha = m_\beta = m \ge 0$. The trait is additive in two diallelic loci $A/a$ and $B/b$ with allelic effects $\mp c_1$ at $A/a$ and $\mp c_2$ at $B/b$, where $c_1, c_2 > 0$ and $c_1 + c_2 = 1$ (so the phenotypic range is $[-1,1]$), and the ratio of locus effects is $\kappa = c_2/c_1$ with $0 < \kappa \le 1$ ($A$ is the major locus). The bound $\kappa > 0$ (both loci affect the trait) is needed below: at $\kappa = 0$, $Ab$ and $aB$ have the same values as $AB$ and $ab$, the condition $0 \le P < \kappa/(1+\kappa)$ in item 3 is empty, and the formula in item 4 divides by zero. In the haploid model the four haplotypes $AB, Ab, aB, ab$ have genotypic values $-1, -\frac{1-\kappa}{1+\kappa}, \frac{1-\kappa}{1+\kappa}, 1$. With haplotype frequencies $x_{i,\gamma}$, linkage disequilibrium $D_\gamma = x_{1,\gamma}x_{4,\gamma} - x_{2,\gamma}x_{3,\gamma}$ and recombination rate $r \ge 0$, the dynamics are

$$\dot x_{i,\gamma} = x_{i,\gamma}\left(w_{i,\gamma} - \bar w_\gamma\right) - \eta_i\,r\,D_\gamma + m\left(x_{i,\gamma^*} - x_{i,\gamma}\right),$$

where $\eta_1 = \eta_4 = -\eta_2 = -\eta_3 = 1$ and $\gamma^*$ is the other deme. Selection is directional (haplotype fitnesses monotone in $G$ in each deme) if and only if $P \ge 1/(1+\kappa)$, and stabilizing otherwise.

**Without migration** ($m = 0$), in a single deme of the haploid model:

1. the monomorphic equilibrium $M_{1,\alpha}$ (fixation of $AB$ in deme $\alpha$; by symmetry $M_{4,\beta}$) is globally asymptotically stable if and only if $P > 1/(1+\kappa)$;
2. there is at most one internal equilibrium $F_\gamma$, and it is unstable whenever it exists;
3. $F_\gamma$ exists exactly when both $M_{2,\gamma}$ and $M_{3,\gamma}$ (fixation of $Ab$ and $aB$) are asymptotically stable, which is the case if and only if $0 \le P < \frac{\kappa}{1+\kappa}$ and $r > \tilde r = \frac{4s(1-\kappa)P}{1+\kappa}$;
4. for uniform selection ($P = 0$), $F_\gamma$ is $\hat p = \hat q = \tfrac12$ with

$$\hat D = \frac{r}{s}\frac{(1+\kappa)^2}{16\kappa} - \sqrt{\frac{1}{16} + \left(\frac{r}{s}\frac{(1+\kappa)^2}{16\kappa}\right)^2}.$$

So a single panmictic haploid deme maintains no stable polymorphism. In the diploid model with $P = 0$, by contrast, single-locus polymorphisms with the major locus polymorphic, $\hat p = \tfrac12 \pm \kappa$ with locus $B$ fixed, can be stable.

## Depends on

- [Gametic linkage disequilibrium](../../../../quantitative-genetics/dominance-linkage-disequilibrium/ld-d.md)

## Expansion

Quadratic selection around an intermediate optimum favours the two haplotypes with intermediate values $Ab$ and $aB$, which are produced from each other only through recombination via the extreme haplotypes; this creates the bistability between $M_2$ and $M_3$ separated by the unstable internal equilibrium. When the optimum moves beyond $1/(1+\kappa)$, the extreme haplotype closest to it becomes fittest and fixes. Migration between demes with opposite optima couples two such systems, and the paper determines the critical migration rates below which full or single-locus polymorphism persists, showing that a concentrated architecture (a major locus tightly linked to a minor one) usually maximizes them.

## Sources

- L. Geroldinger and R. Bürger, "A two-locus model of spatially varying stabilizing or directional selection on a quantitative trait", *Theoretical Population Biology* (2014), Section 2, Eqs. (2.1), (2.2), (2.5)–(2.7), and Section 3, Eqs. (3.1), (3.3b), (3.5), (3.6) and Proposition 3.1. <https://doi.org/10.1016/j.tpb.2014.03.002> (PMC4048038)
