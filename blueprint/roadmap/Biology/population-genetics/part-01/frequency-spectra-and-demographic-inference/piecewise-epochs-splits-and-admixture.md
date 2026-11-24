# Composition across demographic epochs, splits and admixture

In diffusion methods for demographic inference, a history made of epochs with constant parameters, separated by population splits and admixture events, acts on the density $\phi$ of derived alleles at joint population frequencies. Gutenkunst, Hernandez, Williamson and Bustamante (2009, Methods) evolve $\phi$ within an epoch by the multi-population diffusion equation (their equation (1)), whose parameters change with population sizes and migration rates, while splits and mergers change the dimension of $\phi$: if a new population $3$ is formed by admixture with proportion $f$ from population $1$ and $1 - f$ from population $2$, then

$$\phi(x_1, x_2, x_3) = \phi(x_1, x_2)\,\delta\bigl(x_3 - (fx_1 + (1 - f)x_2)\bigr)$$

with $\delta$ the Dirac delta (their equation (2)), and a population is removed by integrating $\phi$ over its frequency. A split of population $1$ into populations $1$ and $3$ is the case $f = 1$, $\phi(x_1)\delta(x_3 - x_1)$. The following composition rules are derived from these operations. If $\Phi_e$ denotes the map that evolves a density through epoch $e$, the density after epochs $e_1, \dots, e_k$ with events $E_1, \dots, E_{k-1}$ between them is $\Phi_{e_k}E_{k-1}\cdots E_1\Phi_{e_1}\phi_0$, by the Chapman–Kolmogorov property of the transition laws within and across epochs; each event is the pushforward of $\phi$ under the deterministic map $(x_1, \dots, x_P) \mapsto (x_1, \dots, x_P, fx_1 + (1 - f)x_2)$ followed, where populations end, by marginalization. The expected joint spectrum is then obtained by binomial sampling from the final density (their equation (3)).

## Depends on

- [Joint site-frequency spectra of several populations](joint-multi-population-sfs.md)
- [Piecewise-constant population-size history](../../../coalescent-theory/site-frequency-spectrum-under-variable-populatio/piecewise-history.md)

## Expansion

1. Piecewise evolution families and their composition across epochs.
2. Splits and admixture as pushforwards under linear maps on frequency vectors, producing densities singular with respect to Lebesgue measure.
3. Marginalization when a population ends.
4. The joint spectrum after a sequence of events by binomial sampling, and the coalescent counterparts of admixture pulses.

## Sources

- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, PLoS Genet. 5 (2009), e1000695, Methods, equations (1)–(3). <https://doi.org/10.1371/journal.pgen.1000695>
