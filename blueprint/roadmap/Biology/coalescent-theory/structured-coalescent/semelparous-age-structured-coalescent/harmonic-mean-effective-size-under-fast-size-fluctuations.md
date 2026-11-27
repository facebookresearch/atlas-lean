# Harmonic-mean effective size under fast fluctuations in a semelparous population

Keep the semelparous age-structured model but let the total population size vary from year to year: at year $t$ in the past the size is $N^{(t)} = x_t N$, where the relative sizes $x_t$ are independent and identically distributed, take finitely many positive values with $\Pr[x_t = x_j] = q_j$, and the demographic parameters $p_i$ and $c_i$, and hence the relative sizes of the age classes, are held fixed. Fluctuations then occur on the fast timescale, one year, while coalescence occurs on the slow timescale of $N$ generations. Taking the limit of the no-coalescence probability over $\lfloor Nt \rfloor$ years shows that the long-term coalescent effective size is the constant-size value scaled by the **harmonic mean** of the yearly relative sizes,

$$N_e^{\text{long}} = \left( \sum_j \frac{q_j}{x_j} \right)^{-1} N_e,$$

with $N_e$ the coalescent effective size of the constant-size model. The limiting ancestral process is still Kingman's coalescent, now on this longer timescale.

## Depends on

- [Coalescent effective size of a semelparous age-structured population](coalescent-effective-size-of-a-semelparous-age-structured-population.md)
- [Rate matrix of Kingman's partition-valued coalescent](../../partition-valued-kingman-coalescent/partition-rate.md)

## Expansion

Conditional on the realized sizes, the probability of no coalescence over $g$ years is a product of per-year factors $1 - \gamma/(x_t N) + o(1/N)$, where $\gamma$ is the per-generation coalescence rate of the constant-size model and the dependence on $x_t$ enters because every age class, and in particular the first, scales linearly with the total size. Independence across years lets the expectation factor over $t$, and $\mathbb E[1 - \gamma/(x N)] = 1 - \gamma\,\mathbb E[1/x]/N$; raising this to the power $\lfloor N t\rfloor$ and letting $N \to \infty$ gives $\exp(-\gamma\,\mathbb E[1/x]\,t)$. The coalescence rate is therefore multiplied by $\mathbb E[1/x] = \sum_j q_j/x_j$, equivalently the effective size is divided by it, which is the harmonic-mean rule familiar from the unstructured Wright–Fisher model with fluctuating size. This separates the two demographic regimes: fluctuations slow compared with coalescence are a deterministic or stochastic time change of the coalescent, whereas fluctuations fast compared with coalescence only renormalize the timescale. It also explains why simulations of salmon populations agree better with a harmonic-mean prediction than with an arithmetic-mean one when each year's spawners contribute in fixed proportion rather than in proportion to their abundance.

## Sources

- C. Cenik, J. Wakeley, "Pacific salmon and the coalescent effective population size", *PLoS ONE* 5 (2010), e13019, <https://doi.org/10.1371/journal.pone.0013019> (PMC2946355). Methods, "The Impact of Fast Fluctuations in the Population Size", and Results.
- P. Sjödin, I. Kaj, S. Krone, M. Lascoux, M. Nordborg, "On the meaning and existence of an effective population size", *Genetics* 169 (2005), 1061–1070, <https://doi.org/10.1534/genetics.104.026799>.
