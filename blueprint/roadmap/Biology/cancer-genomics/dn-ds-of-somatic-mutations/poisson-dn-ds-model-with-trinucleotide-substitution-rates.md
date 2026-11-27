# Poisson dN/dS model with trinucleotide substitution rates

Let $i$ range over substitution classes (in the full trinucleotide model, the $192$ classes given by
the $6$ base substitutions, the $16$ combinations of $5'$ and $3'$ neighbouring bases, and the
transcribed or non-transcribed strand), and let $k \in \{s, m, n, e\}$ denote the functional impact
(synonymous, missense, nonsense, essential splice). For a set of genes in a cohort, let
$L_{i,k}$ be the number of sites at which a class-$i$ substitution has impact $k$, and $n_{i,k}$
the number of observed somatic mutations of class $i$ and impact $k$. The model takes the counts
independent with

$$n_{i,s} \sim \mathrm{Poisson}\bigl(t\, r_i\, L_{i,s}\bigr), \qquad
n_{i,k} \sim \mathrm{Poisson}\bigl(t\, r_i\, L_{i,k}\, \omega_k\bigr) \quad (k \in \{m, n, e\}),$$

where $t > 0$ is the density of substitutions per site, $r_i > 0$ are relative rates with one class
fixed at $r_{i_0} = 1$ for identifiability, and $\omega_m, \omega_n, \omega_e > 0$ are the dN/dS
ratios for each impact class, corrected for mutational spectrum and sequence composition. The joint
likelihood is a Poisson log-linear model with offsets $\log L_{i,k}$, so the maximum likelihood
estimates of $(t, r_i, \omega_k)$ are obtained by Poisson regression. Neutrality corresponds to
$\omega_k = 1$; $\omega_k > 1$ indicates positive and $\omega_k < 1$ negative selection, tested by
likelihood ratio tests such as

$$H_0:\ \omega_m = \omega_n = \omega_e = 1 \quad\text{vs}\quad H_1:\ \omega_m \ \text{and}\ \omega_n = \omega_e \ \text{free},$$

with $2$ degrees of freedom.

## Depends on

- [The ratio dN/dS equals ω](../../phylogenetics/codon-substitution-models-and-dn-ds/d-n-div-d-s.md)

## Remarks

Somatic mutation densities are tiny (typically below $10^{-5}$ per site), so multiple hits per
site are negligible and counts can be modelled directly as Poisson rather than through a codon
substitution process along a tree. Synonymous counts identify $t$ and the $r_i$; each non-synonymous
class then has one extra multiplicative parameter, and since all other factors are shared,
$\hat\omega_k$ is the ratio of observed to neutrally expected non-synonymous mutations. Simplified
spectra (for example a single transition/transversion ratio) give systematically biased
$\hat\omega_k$ under strongly context-dependent mutational signatures, which is why the full
trinucleotide parametrization is used; by AIC it was vastly preferred to a 12-parameter model in all
29 cancer types studied.

## Sources

- I. Martincorena, K. M. Raine, M. Gerstung et al., "Universal Patterns of Selection in Cancer and Somatic Tissues", *Cell* 171 (2017), <https://doi.org/10.1016/j.cell.2017.09.042> (PMC5720395), STAR Methods, subsections "Poisson framework", "Substitution models" and "Likelihood ratio tests for the inference of selection".
