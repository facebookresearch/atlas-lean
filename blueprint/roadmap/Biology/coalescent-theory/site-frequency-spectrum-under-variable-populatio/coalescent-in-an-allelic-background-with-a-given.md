# Coalescent in an allelic background with a given frequency path

Consider a biallelic selected locus whose allele $A$ has a given frequency path $x(t)$, piecewise continuous, on a time window on which $\delta \le x(t) \le 1 - \delta$ for some $\delta > 0$ (or with an explicit truncation at the boundary). Forward in time, $A$ mutates to $B$ at rate $\theta_{AB}/2$ and $B$ to $A$ at rate $\theta_{BA}/2$ per lineage per $M$ generations, and a linked neutral locus recombines with it at rate $\rho/2$.

Backwards in time, a lineage at the neutral locus moves between backgrounds at the rates

- from $A$ to $B$: by mutation at $\frac{\theta_{BA}}{2} \frac{1 - x}{x}$ and by recombination at $\frac{\rho}{2}(1 - x)$;
- from $B$ to $A$: by mutation at $\frac{\theta_{AB}}{2} \frac{x}{1 - x}$ and by recombination at $\frac{\rho}{2} x$;

and each pair of lineages in background $A$ coalesces at rate $1/x$, each pair in $B$ at rate $1/(1 - x)$, with $x = x(t)$. With the [rate matrices for the frozen path](background-coalescent-rate-matrices-for-a-frozen.md), the [time-ordered product limit](time-ordered-product-limit-for-near-identity-mat.md) gives the transition matrices of this time-inhomogeneous continuous-time Markov chain. Fixation and loss of $A$ are separate statements on reduced state spaces, not the substitution $x = 1$ or $x = 0$.

## Depends on

- [Time-ordered product limit for near-identity matrices](time-ordered-product-limit-for-near-identity-mat.md)
- [Rate matrices of the coalescent in an allelic background with a frozen frequency path](background-coalescent-rate-matrices-for-a-frozen.md)

## Expansion

1. The backward rates from the forward mutation and recombination rates and the frequency path.
2. The construction of the time-inhomogeneous chain.
3. Checks: for constant $x$ and $\theta = 0$ this is a two-deme structured coalescent, with detailed balance $x \cdot \frac{\rho}{2}(1 - x) = (1 - x) \cdot \frac{\rho}{2} x$. For constant $x$ at the mutation equilibrium $x = \theta_{BA}/(\theta_{AB} + \theta_{BA})$, the background law $(x, 1 - x)$ of one lineage is stationary.
4. The boundary cases, handled separately.

## Sources

- N. L. Kaplan, T. Darden and R. R. Hudson, The coalescent process in models with selection, *Genetics* 120 (1988), 819–829 (background coalescent).
- R. R. Hudson and N. L. Kaplan, The coalescent process in models with selection and recombination, *Genetics* 120 (1988), 831–840, <https://www.cs.cmu.edu/~epxing/CBML/coalescent1/Hudson_Kaplan88.pdf> (selection and recombination).
