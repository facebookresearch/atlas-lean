# SAFE score from haplotype allele frequency scores

Let a sample consist of $n$ phased haplotypes over a set of segregating sites in a genomic window, coded $1$ for the derived and $0$ for the ancestral allele. For a site $e$ let $c(e)$ be its derived-allele count and $f(e) = c(e)/n$ its frequency. The **haplotype allele frequency (HAF) score** of a haplotype $h$ is

$$\mathrm{HAF}(h) = \sum_{e\,:\, h_e = 1} c(e),$$

the sum of the derived-allele counts of the mutations it carries. Call two haplotypes distinct if their HAF scores differ. For each mutation $e$ define

$$\kappa(e) = \frac{\#\{\text{distinct haplotypes carrying } e\}}{\#\{\text{distinct haplotypes in the sample}\}}, \qquad \phi(e) = \frac{\sum_{h\,:\,h_e = 1} \mathrm{HAF}(h)}{\sum_{h} \mathrm{HAF}(h)},$$

and the **SAFE score** (Selection of Allele Favored by Evolution)

$$\mathrm{SAFE}(e) = \frac{\phi(e) - \kappa(e)}{\sqrt{f(e)\,(1 - f(e))}} \qquad (0 < f(e) < 1).$$

## Depends on

- [Haplotypes carrying an allele at a site](../../coalescent-theory/hudson-kaplan-bound-on-recombination-events/carriers.md)

## Expansion

Under neutral Wright–Fisher evolution both $\kappa(e)$ and $\phi(e)$ behave as estimators of $f(e)$, and in simulations $\phi - \kappa$ has mean zero and variance proportional to $f(1 - f)$, so SAFE is a standardized, approximately Gaussian score under neutrality; these are empirical properties, not theorems. During a sweep, carriers of the favored allele accumulate high HAF scores (their mutations rise in frequency together), which raises $\phi$ for the favored mutation, while the sweep collapses carrier diversity, which lowers $\kappa$. The favored mutation therefore gets a large positive $\phi - \kappa$; mutations private to non-carriers move the other way (higher $\kappa$, lower $\phi$), and mutations older or younger than the favored one on carrier backgrounds fall in between. In simulated sweeps the favored mutation has median SAFE rank at most $3$ among about $250$ variants in a $50$ kb window, but performance degrades for larger windows, where most haplotypes become unique and $\kappa$ loses information.

## Sources

- A. Akbari, J. J. Vitti, A. Iranmehr, M. Bakhtiari, P. C. Sabeti, S. Mirarab and V. Bafna, "Identifying the favored mutation in a positive selective sweep", *Nature Methods* 15 (2018), Online Methods Eqs. (1)–(3), <https://doi.org/10.1038/nmeth.4606> (PMC6231406).
