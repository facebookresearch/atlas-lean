# TreeMix covariance relative to the mean population

Let $X = (X_1, \dots, X_m)$ be the allele frequencies of a SNP in $m$ populations related to an ancestral population of frequency $x_A$ by a population graph, with $\mathbb E X_i = x_A$ for all $i$ and covariance matrix $V = (V_{ij})$ implied by the graph (in TreeMix, $X \approx \mathcal N_m(x_A\mathbf 1, V)$ with $V = x_A(1 - x_A)V_0$, where $V_0$ is the matrix of shared drift of the graph). Let $\bar X = \frac1m\sum_{k=1}^m X_k$ be the mean across populations. Then the covariance of frequencies measured relative to that mean is

$$W_{ij} := \mathbb E\big[(X_i - \bar X)(X_j - \bar X)\big] = V_{ij} - \frac1m\sum_{k=1}^m V_{ik} - \frac1m\sum_{k=1}^m V_{jk} + \frac1{m^2}\sum_{k=1}^m\sum_{l=1}^m V_{kl},$$

i.e. $W = CVC = x_A(1 - x_A)\,C V_0 C$ with the centring matrix $C = I_m - \frac1m\mathbf 1\mathbf 1^{\top}$. The population quantity $W$ still depends on the ancestral frequency through the factor $x_A(1 - x_A)$; what does not is its **empirical estimate** $\hat W_{ij} = \frac1S\sum_s (\hat x_{si} - \bar x_s)(\hat x_{sj} - \bar x_s)$ over SNPs, which uses only observed descendant frequencies, because centring at the observed mean $\bar X$ removes the unknown mean $x_A$. TreeMix fits its predicted $W$ to that estimate.

## Depends on

- [Gaussian surrogate law of population allele frequencies](gaussian-surrogate.md)
- [Drift covariance matrix of lineage weights and edge lengths](drift-cov.md)

## Proof depends on

None beyond bilinearity of covariance and $C\mathbf 1 = 0$, as the Expansion describes.

## Expansion

$X_i - \bar X = (C(X - x_A\mathbf 1))_i$ because $C\mathbf 1 = 0$, so $\mathbb E[(X - \bar X\mathbf 1)(X - \bar X\mathbf 1)^\top] = C V C$, whose entries expand to the displayed formula. Mixture edges enter $V$ through weighted parental contributions: an admixed population with parents $a, b$ and weight $w$ has frequency $wX_a + (1-w)X_b$ plus its own drift. Results, "Properties of the sample covariance", Equations (20)–(24).

## Sources

- J. K. Pickrell, J. K. Pritchard, "Inference of Population Splits and Mixtures from Genome-Wide Allele Frequency Data", PLoS Genetics 8 (2012), e1002967, <https://doi.org/10.1371/journal.pgen.1002967> (PMC3499260).
