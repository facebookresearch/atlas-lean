# Statistical certification of simulators by exact finite-sample tests

Let a simulator produce independent replicates, and let $A$ be an event whose probability $p_0$ under the exact model is known in closed form; for example, for a sample of $n=2$ lineages under [Kingman's coalescent](../../../Biology/coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/hudson-s-algorithm-without-recombination-samples.md) in coalescent time units, $P(T_{\mathrm{MRCA}}>t)=e^{-t}$. Run $B$ independent replicates, let $X$ be the number in which $A$ occurs, so $X\sim\mathrm{Bin}(B,p)$ where $p$ is the simulator's true probability of $A$, and reject at level $\alpha\in(0,1)$ when the [exact two-sided binomial test](README.md) rejects $p=p_0$, for instance when $p_0$ lies outside the [Clopper–Pearson interval](clopper-pearson-coverage.md) at level $\alpha$. Then:

- if the simulator is exact ($p=p_0$), the probability of rejection is at most $\alpha$, for every $B$;
- if $p\ne p_0$, the probability of rejection tends to $1$ as $B\to\infty$;
- several such checks on events $A_1,\dots,A_c$ combine with familywise error at most $\alpha$ by the [Bonferroni procedure](../bonferroni-correction/measure-bonferroni-familywise-error-le.md) (each test at level $\alpha/c$) or by [Holm's procedure](../holm-bonferroni-method/measure-holm-familywise-error-le.md).

For example, a simulator that returns a biased coin with probability $p\ne p_0$ of $A$ is rejected with probability tending to $1$.

## Depends on

- [Coverage of the Clopper–Pearson interval](clopper-pearson-coverage.md)
- [The Bonferroni procedure controls the FWER](../bonferroni-correction/measure-bonferroni-familywise-error-le.md)
- [Holm's procedure controls the FWER](../holm-bonferroni-method/measure-holm-familywise-error-le.md)
- [Clopper–Pearson lower confidence limit](clopper-pearson-lower.md)
- [Clopper–Pearson upper confidence limit](clopper-pearson-upper.md)

## Proof depends on

- [Hudson's algorithm without recombination samples Kingman's coalescent](../../../Biology/coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/hudson-s-algorithm-without-recombination-samples.md)

## Expansion

A proof page must establish: the size bound from the coverage of the Clopper–Pearson interval (or from validity of the exact binomial p-values); consistency against a fixed $p\ne p_0$, since $X/B\to p$ almost surely and both Clopper–Pearson endpoints converge to $p$; the familywise combination; and the two-lineage example, where $T_{\mathrm{MRCA}}$ is exponential with rate $1$ under the exact sampler.

## Sources

- J. Kelleher, A. M. Etheridge and G. McVean, *Efficient coalescent simulation and genealogical analysis for large sample sizes*, PLoS Computational Biology 12 (2016), e1004842, <https://ibg.colorado.edu/cdrom2019/evansL/simulation/papers/Kelleher%20et%20al.%202016%20MSPRIME%20coalescent%20simulation.PDF> (validation of a simulator against exact results; background).
