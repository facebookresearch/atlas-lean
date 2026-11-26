# Frequency-weighted mutation-accumulation rate

Consider a population evolved for $P$ passages (generations or replication cycles) from an isogenic ancestor, sequenced at the end. For a genomic region $r$ of length $L_r$ sites, let $f_1, \dots, f_{k_r}$ be the population frequencies of the de novo mutations observed in $r$. The frequency-weighted mutation-accumulation rate of $r$ is

$$M_a(r) = \frac{\sum_{i=1}^{k_r} f_i}{P\, L_r},$$

in units of mutations per site per passage. Assume infinite sites (no site mutates twice and there is no back mutation), that new mutations arise at rate $\mu$ per site per passage in each genome, and that all mutations in $r$ are neutral. Then, whatever the demography (bottlenecks, burst sizes, population sizes),

$$\mathbb{E}\Big[\sum_i f_i\Big] = \mu L_r P, \qquad \text{so} \qquad \mathbb{E}[M_a(r)] = \mu.$$

Selection biases $M_a$: positively selected mutations raise it above $\mu$ and purifying selection lowers it, which is why $M_a$ is compared between synonymous and non-synonymous sites. Detection thresholds on frequency or read support remove low-frequency mutations and bias $M_a$ downwards.

## Remarks

The summed frequency $\sum_i f_i$ equals the mean, over genomes in the population, of the number of derived mutations in $r$ that each genome carries. Under neutral reproduction the frequency of every existing mutation is a martingale: sampling and bottlenecks change it randomly but not in expectation. Each passage, mutation adds on average $\mu L_r$ new derived sites per genome, so the expected mean number of derived mutations per genome increases by exactly $\mu L_r$ per passage, giving $\mu L_r P$ after $P$ passages. Infinite sites ensures that new mutations do not overwrite existing ones. The neutral expectation of the full site frequency spectrum, by contrast, depends on demography, and is obtained by forward simulation of growth, mutation and bottleneck cycles at the estimated rate.

## Sources

- M. Amicone, V. Borges, M. J. Alves, J. Isidro, L. Zé-Zé, S. Duarte, L. Vieira, R. Guiomar, J. P. Gomes and I. Gordo, Mutation rate of SARS-CoV-2 and emergence of mutators during experimental evolution, *Evol. Med. Public Health* 10 (2022), 142–155, <https://doi.org/10.1093/emph/eoac010>, PMCID PMC8996265 (Methodology, mutation-accumulation rate $M_a(r)$ and neutral simulations).
