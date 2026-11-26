# Effective size of an endemic SIR pathogen population

In a Wright–Fisher population of size $N$ whose offspring distribution has variance $\sigma^2$, with generations of length $\tau$, $A$ lineages coalesce at rate $\binom{A}{2}/(N_e \tau)$ with $N_e = N/\sigma^2$.

Consider an SIR infection at endemic equilibrium with $I$ infected hosts, recovery rate $\gamma$ and host mortality negligible relative to $\gamma$, so that each infection has, on average, exactly one secondary case ($\beta S^* = \gamma$ at the equilibrium susceptible fraction $S^*$). The offspring number of an infected host is Poisson given its infectious period $D \sim \mathrm{Exp}(\gamma)$, with mean $\beta S^* D$. Then:

1. the individual mean offspring $\beta S^* D = \gamma D$ is exponentially distributed with mean $1$, hence variance $1$;
2. the offspring variance is $\sigma^2 = 1 + 1 = 2$, so $N_e = I/2$;
3. with generation time $\tau = 1/\gamma$, the coalescence rate is

$$\binom{A}{2} \frac{1}{N_e \tau} = \binom{A}{2} \frac{2\gamma}{I},$$

which coincides with the SIR epidemic coalescent rate $\binom{A}{2}\, 2\beta S^*/I$ at equilibrium.

## Depends on

- [Coalescent rate under SIR epidemic dynamics](coalescent-rate-under-sir-epidemic-dynamics.md)

## Expansion

For a mixed Poisson offspring number $X$ with random mean $\nu$, the law of total variance gives $\mathrm{Var}(X) = \mathbb{E}[\nu] + \mathrm{Var}(\nu)$, which is $1 + 1$ when $\nu$ is exponential with mean one. The factor $2$ means that an endemic SIR pathogen population behaves like a Wright–Fisher population of half its census size per infectious period. The same argument gives coalescence rates for models with superspreaders, exposed classes or non-exponential infectious periods: each changes $\sigma^2$ and $\tau$.

## Sources

- E. M. Volz, K. Koelle, T. Bedford, "Viral phylodynamics", PLoS Computational Biology 9(3) (2013) e1002947, Methods, "Coalescent Theory and Phylodynamics", subsection "Compartmental models" (endemic equilibrium and offspring variance), <https://doi.org/10.1371/journal.pcbi.1002947> (PMC3605911).
