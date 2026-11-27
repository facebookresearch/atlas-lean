# False-positive rate of a k-of-n variant call rule

At a given time point, $n$ patient-specific single-nucleotide variant assays are run on cell-free DNA. Under the null hypothesis that no tumour DNA is present, model the assays as independent, each called positive with probability $p \in (0,1)$, the per-assay false-positive rate fixed by a confidence threshold calibrated against negative control samples and against samples not expected to carry that variant. The sample is called positive for circulating tumour DNA when at least $k$ assays are positive. Its false-positive rate, the probability that the sample is called positive given that no tumour DNA is present, is the binomial upper tail

$$\mathrm{FPR}(k, n, p) \;=\; \sum_{i=k}^{n} \binom{n}{i} p^{i} (1-p)^{n-i} .$$

Properties, for fixed $p \in (0,1)$: $\mathrm{FPR}$ is strictly decreasing in $k$ for $1 \le k \le n$, strictly increasing in $n$ for fixed $k \ge 1$, and strictly increasing in $p$. Consequently, holding the sample-level false-positive rate at a target $\alpha$ while enlarging the panel requires decreasing $p$, that is tightening the per-assay threshold, or increasing $k$.

Worked values from a panel of $n = 103$ assays with per-assay rate $p = 0.0011$:

$$\mathrm{FPR}(1) = 1 - (1-p)^{n} = 0.1072, \qquad \mathrm{FPR}(2) = 1 - (1-p)^{n} - np(1-p)^{n-1} = 0.0059 .$$

So, for a sample with no tumour DNA, at least one assay of the panel is positive with probability about $10.7\%$ at each time point, and at least two with probability below $1\%$. These are panel-level rates under the null hypothesis. They are not the probability that an observed positive call is spurious, which also depends on the prevalence of residual disease and on the sensitivity of the assays.

## Depends on

- [Binomial upper tail probability](../detection-power-for-somatic-mutations/upper-tail.md)

## Proof sketch

Independence across assays is the modelling assumption that makes the tail exact; it is reasonable when the dominant error source is position-specific sequencing and amplification noise, calibrated separately at each locus, rather than a shared contamination event, which would correlate the calls and inflate the true tail above the binomial value.

Monotonicity in $k$ is immediate from dropping nonnegative terms. Monotonicity in $n$ follows from the coupling that adds one further independent assay: the event "at least $k$ positives among the first $n$" implies the same event among $n+1$ assays, and the inclusion is strict with positive probability. This is why the design that was adequate for a panel of about twenty variants required a tightened per-assay threshold when the panel grew to one hundred: the threshold was raised until the expected number of false calls, measured by applying the current threshold to negative samples and extrapolating that rate to the eligible positions of the positive samples, fell below the design target.

The same tail controls sensitivity in the other direction. A rule demanding $k$ positives cannot detect a tumour whose variants are present at allele fractions where fewer than $k$ assays are expected to fire, so raising $k$ to buy specificity costs detection of the lowest-burden samples: with per-assay sensitivity above $99\%$ at variant allele fractions above $0.1\%$, the two-variant rule remains sensitive for samples carrying at least two trackable clonal variants, which is why clonal variants dominate panel design and subclonal clusters are tracked with several variants each.

## Sources

- C. Abbosh, N. J. Birkbak, G. A. Wilson, M. Jamal-Hanjani, T. Constantin, R. Salari, J. Le Quesne, D. A. Moore, S. Veeriah, R. Rosenthal et al., "Phylogenetic ctDNA analysis depicts early-stage lung cancer evolution", Nature 545 (2017) 446-451, Methods, "Plasma SNV calling algorithm", Extended Data Fig. 1b, and the reported rates for the 103-assay panel, <https://doi.org/10.1038/nature22364> (PMC5812436).
