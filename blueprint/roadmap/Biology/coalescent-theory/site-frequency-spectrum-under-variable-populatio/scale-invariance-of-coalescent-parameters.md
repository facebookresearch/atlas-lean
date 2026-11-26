# Scale invariance of coalescent time, population size and mutation rate

In coalescent models, the distribution of genetic data from a contemporaneous sample depends on the population-size history $N(g)$ ($g$ in generations), the per-generation mutation rate $\mu$ and the recombination rate $r$ only through scaled quantities: replacing $N(g)$ by $cN(g/c)$, $\mu$ by $\mu/c$ and $r$ by $r/c$, for any $c > 0$, leaves the law of the data unchanged. Concretely, the data depend on $\theta = 4N_0\mu$, $\rho = 4N_0 r$ and the relative history $\eta(t) = N(2N_0 t)/N_0$ in coalescent units; so sizes in individuals and times in generations or years are identifiable only with external calibration of $\mu$ (or $r$) and of the generation time (Nordborg 2001: only scaled parameters can be estimated from polymorphism data, and statements about population numbers or ages in generations need external information; Bhaskar and Song 2014; Terhorst and Song 2015).

## Expansion

1. The scaled parametrization: reference size $N_0$, coalescent time units of $2N_0$ generations, $\theta$, $\rho$ and $\eta$.
2. The invariance: the joint law of genealogies (in coalescent units) and mutations depends on $(\theta, \rho, \eta)$ only, and the transformation $(N(\cdot), \mu, r) \mapsto (cN(\cdot/c), \mu/c, r/c)$ leaves these fixed.
3. Consequences: what is identifiable from data alone (the scaled history), and what calibration (mutation rate per generation and generation time) is needed to report sizes in individuals and times in years.
4. The same invariance for serially sampled data, where sampling dates in years add calibration.

## Sources

- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493. <https://arxiv.org/abs/1309.5056>
- J. Terhorst and Y. S. Song, Fundamental limits on the accuracy of demographic inference based on the sample frequency spectrum, Proc. Natl. Acad. Sci. USA 112 (2015), 7677–7682. <https://arxiv.org/abs/1505.04228>
- M. Nordborg, Coalescent theory, in *Handbook of Statistical Genetics*, Wiley, 2001 (preprint of March 2000). <https://doi.org/10.1002/0470022620.bbc21>
