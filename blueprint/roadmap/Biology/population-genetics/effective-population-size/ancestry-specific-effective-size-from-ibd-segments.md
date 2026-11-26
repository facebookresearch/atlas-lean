# Ancestry-specific effective population size from IBD segments

Let a sample of $n$ diploid individuals come from an admixed population, and fix one ancestral source population. For generations $g$ before the present (after admixture began), define the ancestry-specific coalescence probability $q_g$ as the probability that two distinct lineages, both of the given ancestry and not yet coalesced, coalesce in generation $g$; the ancestry-specific effective size is

$$N_g=\frac1{2q_g}.$$

Given genealogies, $q_g$ is estimated by pooling over trees $i$:

$$\hat q_g=\frac{\sum_i c_i}{\sum_i b_i(b_i-1)/2},$$

where $b_i$ is the number of lineages of that ancestry in generation $g$ and $c_i$ the number of coalescences among them. From data, IBD segments of length at least a threshold are assigned fractionally to coalescence times according to their full length and the current size history, as in IBD-based $N_e$ estimation, but only the IBD of the given ancestry is counted, and the number of haplotype pairs is replaced by the ancestry-adjusted count

$$\sum_{i=1}^{n-1}\sum_{j=i+1}^n 4\,p_ip_j,$$

where $p_i$ is individual $i$'s genome-wide proportion of that ancestry. Assigning each IBD segment to an ancestry at random with probabilities equal to its local-ancestry proportions gives an unbiased estimate of the total IBD length of that ancestry.

## Remarks

In a Wright–Fisher population of $N$ diploids two lineages coalesce with probability $1/(2N)$ per generation, which motivates $N_g=1/(2q_g)$. Expected total IBD from generation $g$ is proportional to the number of haplotype pairs that could produce it; two haplotypes can be IBD for a given ancestry only where both carry it, and with independent local ancestry in unrelated individuals a random haplotype pair from individuals $i$ and $j$ is jointly of that ancestry on a fraction $p_ip_j$ of the genome, with four haplotype pairs per individual pair. The segment's full length, not its ancestry-restricted pieces, must be used for dating, since length measures time to the common ancestor. Close relatives inflate recent IBD and must be removed using genome-wide IBD before the ancestry-specific analysis.

## Depends on

- [Expected IBD per generation and the IBDNe moment update](../../coalescent-theory/skyline-plot-estimates-of-population-size/ibd-based-estimation-of-recent-effective-size/expected-ibd-per-generation-and-the-ibdne-update.md)

## Sources

- S. R. Browning, B. L. Browning, M. L. Daviglus et al., "Ancestry-specific recent effective population size in the Americas", PLoS Genet. 14 (2018) e1007385, Methods ("Simulated data", "Ancestry-specific effective population size estimation", "Ancestry-adjusted number of pairs of sampled haplotypes"), <https://doi.org/10.1371/journal.pgen.1007385>, PMCID PMC5967706.
