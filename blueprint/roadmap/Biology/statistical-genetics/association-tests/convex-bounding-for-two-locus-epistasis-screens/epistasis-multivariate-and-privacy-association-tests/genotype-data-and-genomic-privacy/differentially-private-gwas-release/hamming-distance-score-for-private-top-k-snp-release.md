# Hamming distance score for private top-K SNP release

Consider a biallelic SNP in a case–control study with $R$ cases, $S$ controls and $N = R + S$, where cases (controls) have $r_0, r_1, r_2$ ($s_0, s_1, s_2$) individuals with $0, 1, 2$ copies of the minor allele. The **allelic test statistic** (the Cochran–Armitage trend test for an additive model, equal to Pearson's $\chi^2$ on the $2 \times 2$ allele table) is

$$Y_A = \frac{2N\big[(2r_0 + r_1)S - (2s_0 + s_1)R\big]^2}{R\,S\,(2n_0 + n_1)(n_1 + 2n_2)}, \qquad n_g = r_g + s_g .$$

With control data public and $R, S$ fixed, write $x = 2r_0 + r_1$ (major alleles among cases) and $n_{10} = 2s_0 + s_1$; then

$$Y_A(x) = \frac{2N\,(xS - n_{10}R)^2}{R\,S\,(x + n_{10})(2N - x - n_{10})}.$$

**Lemma (monotonicity).** $Y_A$ is increasing in $x$ when $xS - n_{10}R > 0$ and decreasing when $xS - n_{10}R < 0$.

A **change** to the genotype table alters one case's genotype, i.e. moves $(r_0, r_1)$ by one of six unit steps within $r_0, r_1 \ge 0$, $r_0 + r_1 \le R$. For a significance threshold $c$, the **shortest Hamming distance** of a table $D$ is the least number of changes that make $Y_A$ cross $c$ (with the convention below when no table can cross). By the lemma, $Y_A$ depends on the table only through $x$, decreases on $x < n_{10}R/S$ and increases on $x > n_{10}R/S$, so the shortest distances are found by walking along the $x$ axis, changing $x$ by $2$ per step through $r_0$ while possible and by $1$ per step otherwise (Propositions 2 and 3 of the source).

- *Insignificant table* ($Y_A(D) < c$). Both directions must be tried: $d^- = \min\{H_1, H_2\}$, where $H_1$ counts the changes that decrease $x$ (first decreasing $r_0$, then, once $r_0 = 0$, decreasing $r_1$) until the table becomes significant, and $H_2$ counts the changes that increase $x$ (first increasing $r_0$, then, once $r_0 + r_1 = R$, replacing a heterozygous case by a homozygous one at each step) until it becomes significant; a direction along which $Y_A$ never reaches $c$ contributes $\infty$. If no table with the given control data and case count is significant, so that both directions give $\infty$, the source instead sets $d^- = \min\{1 + d_1, 1 + d_2\}$, where $d_1$ and $d_2$ are the least numbers of changes that take $D$ to the extreme tables with the smallest ($x = 0$) and largest ($x = 2R$) values of $x$.
- *Significant table* ($Y_A(D) \ge c$). Only the direction toward the null line can make the table insignificant (the other contributes $\infty$), and $d^+$ is the number of changes that move $x$ toward $n_{10}R/S$ until $Y_A$ drops below $c$.

The **Hamming distance score** is $h = -d^-$ if $Y_A(D) < c$ and $h = d^+ - 1$ if $Y_A(D) \ge c$.

**Corollary.** The Hamming distance score has sensitivity $1$: changing one participant changes $h$ by at most $1$.

Hence releasing $K$ SNPs by the exponential mechanism, sampling SNP $i$ with probability proportional to $\exp\big(\varepsilon\, q_i / (2Ks)\big)$ without replacement for $K$ rounds with $q_i = h_i$ and $s = 1$, is $\varepsilon$-differentially private.

## Depends on

- [Differential privacy](../../../../../../../ComputerScience/cryptography/differential-privacy/differentially-private.md)
- [Exponential mechanism](../../../../../../../ComputerScience/cryptography/laplace-and-exponential-mechanisms/exp-mechanism.md)
- [Pearson's chi-squared statistic of a 2 × 2 table](../../../../../genomic-prediction-from-summary-statistics/pearson2x2.md)

## Proof depends on

- [The exponential mechanism is differentially private](../../../../../../../ComputerScience/cryptography/laplace-and-exponential-mechanisms/exp-mechanism-differentially-private.md)

## Expansion

A mechanism $K$ is $\varepsilon$-differentially private if $\Pr(K(D) \in A) \le e^{\varepsilon} \Pr(K(D') \in A)$ for all databases differing in one individual. The exponential mechanism's guarantee scales with the sensitivity of the score; the $\chi^2$ statistic has a data-dependent sensitivity bound, whereas an exact shortest Hamming distance has sensitivity $1$ by construction, which earlier approximate implementations lost. Monotonicity reduces the exact computation from a search over all change sequences to walking along the $x$ axis, so the score costs $O(R)$ per SNP. Utility is measured by the overlap between the released and true top-$K$ sets.

## Sources

- F. Yu and Z. Ji, "Scalable privacy-preserving data sharing methodology for genome-wide association studies: an application to iDASH healthcare privacy protection challenge", BMC Medical Informatics and Decision Making 14 (Suppl 1) (2014), S3, Definitions 1–6, Algorithms 1–2, Lemma 1, Propositions 2–3 and Corollary 4, <https://doi.org/10.1186/1472-6947-14-S1-S3>, PMCID: PMC4290802.
