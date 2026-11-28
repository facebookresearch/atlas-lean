# Recovery of a recessive allele in a Mendelian diploid model

**Model.** A diploid hermaphroditic population carries three alleles at one locus with dominance order $a < A < B$, so the genotype space is $\mathcal{G} = \{aa, aA, AA, aB, AB, BB\}$ and the phenotypes are $a = \{aa\}$, $A = \{aA, AA\}$ and $B = \{aB, AB, BB\}$. Individuals reproduce by random mating with Mendelian segregation at common fertility $f > 0$, die naturally at rate $D + \Delta$ (phenotype $a$), $D$ (phenotype $A$) or $D - \Delta$ (phenotype $B$) with $0 < \Delta < D$, and die from logistic competition at rate $c\,n_j$ caused by each genotype $j$. Phenotypes $a$ and $B$ neither mate nor compete with each other, and a parameter $0 \le \eta < c$ lowers the competition between $BB$ and $aA$ to $c - \eta$. In the large-population limit (carrying capacity $K \to \infty$, densities $n_i = N_i/K$) the stochastic process converges on finite time intervals to the solution of the ODE system

$$\dot n_i = b_i(n) - \Big(D_i + \sum_{j\in\mathcal{G}} c_{i,j}\,n_j\Big)\,n_i, \qquad i \in \mathcal{G},$$

where $b_i(n)$ is the Mendelian birth rate of genotype $i$ (a sum of products of parental allele frequencies divided by the size of the relevant mating pool). A monomorphic $uu$ population has equilibrium density $\bar n_u = (f_{uu} - D_{uu})/c_{uu,uu}$.

**Initial condition.** The resident is $AA$ at $\bar n_A - O(\varepsilon) \le n_{AA}(0) \le \bar n_A$, the unfit recessive allele survives in heterozygotes, $n_{aA}(0) = \varepsilon$ and $n_{aa}(0) = O(\varepsilon^2)$, and a new dominant mutant enters with $n_{AB}(0) = \varepsilon^3$, $n_{BB}(0) = n_{aB}(0) = 0$.

**Theorem.** Assume (C1) $\Delta$ is sufficiently small, (C2) $f$ is sufficiently large and (C3) $0 \le \eta < c/2$. Then the solution converges to the fixed point $p_{aB}$ at which the two homozygote populations $aa$ and $BB$ coexist (each at its monomorphic equilibrium) and all other genotypes vanish. For any fixed $\delta > 0$, as $\varepsilon \to 0$ it enters the $\delta$-neighborhood of $p_{aB}$ within time

$$O\!\left(\varepsilon^{-1/(1+\eta\bar n_B-\Delta)}\right).$$

Moreover:

1. if $\eta = 0$, the total amount of allele $a$ first decays to order $\varepsilon^{1+\Delta/(1+\Delta)}$ before the $aa$ population grows to order $1$;
2. if $\eta > 4\Delta/\bar n_B$, the amount of allele $a$ stays bounded below by order $\varepsilon$ for all $t > 0$.

The point $p_{aB}$ is non-hyperbolic (its Jacobian has a double zero eigenvalue), but it is stable, and a local center reduction shows that the flow approaches it at speed $1/t$.

## Expansion

The proof follows four phases. First, the fitter $AB$ heterozygote grows exponentially at rate $\Delta$ while $aa$, $aA$ stay small and $n_{BB} \le n_{AB}^2$. Second, the $B$ allele sweeps through the $A$ phenotype: the sum $\Sigma_{aA,aB} = n_{aA} + n_{aB}$ is controlled by $\dot\Sigma_{aA,aB} \le n_{aA}\big(\eta n_{BB} - \Delta\,\tfrac{n_{AB}+O(\Delta n_{AA})}{n_{AB}+2n_{AA}}\big)$ and $\dot\Sigma_{aA,aB} \ge n_{aA}(\eta n_{BB} - \Delta - O(\delta))$, so the $a$ allele is only slowly eroded, and for $\eta > 4\Delta/\bar n_B$ it eventually increases. Third, once $AA$ has been displaced, the $aa$ homozygote, which does not compete with the $B$ phenotype, regrows exponentially from its quadratic reservoir $n_{aa} \asymp \Sigma_{aA,aB}^2$. Fourth, a local center reduction at the non-hyperbolic point shows convergence to $p_{aB}$. The mechanism is genetic robustness: sexual reproduction keeps a recessive allele hidden in heterozygotes long enough for a later mutation to remove its competitor and let the pure $aa$ genotype reinvade.

## Sources

- Anton Bovier, Loren Coquille and Rebecca Neukirch, "The recovery of a recessive allele in a Mendelian diploid model", *J. Math. Biol.* 77(4) (2018), 971–1033. <https://doi.org/10.1007/s00285-018-1240-z>
- Preprint version (the locators in this item follow its numbering): Anton Bovier, Loren Coquille and Rebecca Neukirch, "The recovery of a recessive allele in a Mendelian diploid model", arXiv:1703.02459 (2017), Section 2 (model, Proposition 2.3), Theorem 3.1, Section 3.1 (linear stability), Proposition 4.17, Corollary 4.18 and Theorem 4.30, <https://doi.org/10.48550/arXiv.1703.02459>.
