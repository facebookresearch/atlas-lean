# Germline-versus-somatic classification log-odds score

Let a candidate variant allele $m$ pass the [tumour log-odds test](tumour-variant-lod-with-explicit-allele-fraction.md). Using the per-read likelihood $L[M^m_f]$ from that test, but evaluated on the reads of the matched normal sample, compare the model $M_0$ (variant absent from the normal) with $M^m_{0.5}$ (variant present as a germline heterozygote, allele fraction set conservatively to $1/2$). The normal log-odds score is

$$\mathrm{LOD}_N = \log_{10}\frac{L_N[M_0]}{L_N[M^m_{0.5}]} .$$

The variant is declared **somatic** when the posterior odds of "absent from the normal" exceed $\delta_N$, that is, when

$$\mathrm{LOD}_N \ \ge\ \theta_N = \log_{10}\delta_N - \log_{10}\frac{P(\text{somatic})}{P(\text{germline})} .$$

With $\delta_N = 10$ and a somatic prior $P(\text{somatic}) = 3\times 10^{-6}$ per base:

- at sites not known to be polymorphic, $P(\text{germline}) = 5\times 10^{-5}$ (about 50 private germline variants per megabase), giving $\theta_N = 1 - \log_{10}(0.06) \approx 2.2$;
- at known polymorphic sites, $P(\text{germline}) = 0.095$ (95% of an individual's roughly $3\times10^6$ variants falling among roughly $3\times 10^7$ catalogued sites), giving $\theta_N = 1 - \log_{10}(3.16\times10^{-5}) \approx 5.5$.

A variant is left unclassified ("variant") when the power of the normal data to reach $\theta_N$ against a heterozygote is below 95%.

## Depends on

- [Tumour variant log-odds score with an explicit allele fraction](tumour-variant-lod-with-explicit-allele-fraction.md)

## Expansion

The ratio is inverted relative to the tumour test because the claim to be established is absence: a large $\mathrm{LOD}_N$ means the normal reads are much better explained by noise alone than by a heterozygous germline allele. $\delta_N$ is set higher than the tumour threshold because a misclassified germline variant recurs across patients at population frequency and so contaminates downstream recurrence analysis far more than a single false somatic call. Using a site-specific prior raises the bar exactly where germline variation is common: about 8 normal reads suffice at private sites but about 19 at catalogued polymorphic sites.

## Sources

- K. Cibulskis, M. S. Lawrence, S. L. Carter, et al., "Sensitive detection of somatic point mutations in impure and heterogeneous cancer samples", Nature Biotechnology 31 (2013), Online Methods ("Variant classification") and Results ("Variant classification"), <https://doi.org/10.1038/nbt.2514> (PMC3833702).
