# Joint genealogies in a finite admixed population and the stationary variance of admixture fractions

**Model.** A diploid, biparental Wright–Fisher population of $N_t$ individuals is founded by, and may keep receiving migrants from, two source populations $S_1, S_2$: in generation $t$ each parent of an admixed individual is drawn from $S_1$ with probability $s_1(t)$, from $S_2$ with probability $s_2(t)$, and from the admixed population with probability $h(t) = 1 - s_1(t) - s_2(t)$. Chromosomes are segments $[0,\Lambda]$ (in morgans) with recombination between loci $\lambda_1, \lambda_2$. Sample $n$ alleles at loci $\boldsymbol\lambda$ and trace them back, keeping track of which alleles sit in the same individual and on the same parental chromosome, until each lineage enters a source population. This *joint gene genealogy* $G$ records both physical linkage and shared parental histories.

**Theorem (structure).** $G$ is a time-reversed absorbing Markov chain on configurations of alleles grouped by individual and chromosome, absorbed when every lineage has reached a source population; its one-generation transition probabilities are explicit products of source-choice probabilities $s_1(t), s_2(t)$, within-population parent choices $h(t)/(2N_t)$, and recombination probabilities. Moments of the admixture fraction $H_{S_1}$ of a sampled individual and of the absorption time follow from the absorption matrices $M_\tau(\boldsymbol\lambda)$; in particular $\mathbb{E}[H^p_{S_1}]$ is an average over $p$ loci of absorption probabilities of $p$-allele configurations into $S_1$.

**Theorem (stationarity).** If after some generation the population has constant size $N$ and constant source contributions $s_1, s_2$, then $M_\tau(\boldsymbol\lambda) \to M(\boldsymbol\lambda)$ as $\tau \to \infty$ for every $n$ and $\boldsymbol\lambda$, and the admixture fraction $H^{(\tau)}_{S_1}$ of a random individual converges in distribution. Under isolation ($s_1 = s_2 = 0$ after foundation) the limit retains the founding contributions; under ongoing gene flow ($s_1 + s_2 > 0$) earlier contributions are progressively erased and absorption times converge to an a.s. finite limit.

**Proposition (isolation with a rigid chromosome segment).** Let the admixed population be isolated since foundation with founding contribution $s_1(0)$, and let a short segment recombine exactly once per generation with probability $\rho_0$ (crossover position uniform). With $I = (N+1)\rho_0$,
$$\mathbb{E}H_{S_1} = s_1(0), \qquad \operatorname{Var} H_{S_1} = s_1(0)\big(1 - s_1(0)\big)\,f(I), \qquad f(I) = \frac{(1+2I)\log(1+2I) - 2I}{2I^2}.$$
$f$ decreases strictly from $f(0^+) = 1$ (no recombination: each replicate fixes one ancestry, a Bernoulli variance) to $0$, with $f(I) \sim \log I / I$ as $I \to \infty$, recovering the unlinked large-population limit.

## Depends on

- [Decay of admixture linkage disequilibrium over generations](../admixture-linkage-disequilibrium/linkage-diseq-admixed.md)

## Expansion

Each generation back, every lineage independently picks a parent; the parent is a source individual (absorption) or an admixed individual, and alleles carried by the same individual move to the same or different parental chromosomes according to the recombination probabilities. Because all choices are made per generation from a finite population, two alleles can share parents without being physically linked, which is the dependence the model isolates. With constant parameters the transient part of the chain is time-homogeneous and its absorption matrix converges. For two alleles on a rigid segment under isolation, the chain is ergodic on non-absorbed states; solving the two-allele absorption equations and integrating over loci gives the variance, which depends on $N$ and $\rho_0$ only through $I$, the ratio of recombination to coalescence.

## Sources

- G. Dousson Lys, C. Coron, T. Mary-Huard and P. Verdu, "How shared pedigrees shape gene genealogies in finite admixed populations", arXiv:2611.18781 (2026), Theorems 1, 2, Propositions 1, 2, Corollaries 1, 2 and Appendices E–F, <https://doi.org/10.48550/arXiv.2611.18781>.
