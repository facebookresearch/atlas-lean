# Probability of evolutionary rescue from de novo mutations

Consider a large population of wild-type cells, initially $\bar N$ in number, each dividing at rate $\lambda_0$ and dying at rate $\mu_0 > \lambda_0$, so that the wild-type count is approximated deterministically by $N(t) = \bar N e^{-(\mu_0 - \lambda_0)t}$. At each division a mutant lineage arises with probability $\nu$ (for a gene on $n$ plasmid copies mutating with probability $u$ per copy, $\nu = un$ to first order), and a mutant lineage founded by one mutant cell escapes stochastic loss with probability $p_{\mathrm{est}}$, independently of other lineages while mutants are rare.

**Proposition.** If successful mutant lineages arise as a Poisson process with intensity $\nu\lambda_0 N(t)\,p_{\mathrm{est}}$, the probability that the population is rescued is

$$P_{\mathrm{rescue}} \approx 1 - \exp\Big(-\int_0^\infty \nu\lambda_0 N(t)\,p_{\mathrm{est}}\,dt\Big) = 1 - \exp\Big(-\frac{\nu\lambda_0\bar N}{\mu_0 - \lambda_0}\,p_{\mathrm{est}}\Big).$$

In particular, for a gene on $n$ plasmid copies with wild-type rates independent of $n$, rescue is more likely with copy number $n_1$ than with $n_2$ if and only if $n_1 p_{\mathrm{est}}(n_1) > n_2 p_{\mathrm{est}}(n_2)$.

## Depends on

This node has no prerequisites.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

The number of successful mutations is Poisson with mean equal to the integrated intensity, and rescue fails exactly when this number is zero, so $P_{\mathrm{rescue}} = 1 - e^{-\text{mean}}$. The integral of the exponentially decaying wild-type population is $\bar N/(\mu_0 - \lambda_0)$. The comparison across copy numbers follows because $1 - e^{-x}$ is strictly increasing and every other factor is common. The approximation ignores mutants already present (standing variation), assumes at most one mutated copy per division, and treats establishment as independent of the declining wild type, which is accurate when $\bar N$ is large and mutants are rare.

## Sources

- M. Santer and H. Uecker, "Evolutionary Rescue and Drug Resistance on Multicopy Plasmids", Genetics 215 (2020), 847–868, section "The Model", Equations 2–3, <https://doi.org/10.1534/genetics.119.303012> (PMC7337077).
- H. A. Orr and R. L. Unckless, "Population extinction and the genetics of adaptation", American Naturalist 172 (2008), 160–169, <https://doi.org/10.1086/589460>.
