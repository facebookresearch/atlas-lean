# Three-class Gaussian mixture of run-of-homozygosity lengths

Given the lengths of all [runs of homozygosity](lod-score-of-autozygosity-for-calling-runs-of-homozygosity.md) called in a population, fit by maximum likelihood (EM) a mixture of three univariate Gaussian distributions with free weights, means and variances, and assign each run to its most probable component. Order the components by mean as classes A, B, C and let $A_{\min}, A_{\max}, B_{\min}, B_{\max}, C_{\min}, C_{\max}$ be the smallest and largest run lengths assigned to each. If the three classes occupy disjoint intervals of the real line, define the class boundaries

$$b_{AB} = \frac{A_{\max} + B_{\min}}{2}, \qquad b_{BC} = \frac{B_{\max} + C_{\min}}{2}.$$

Class A (short, tens of kb) is interpreted as homozygosity for ancient haplotypes contributing to local linkage disequilibrium, class B (hundreds of kb to a few Mb) as background relatedness from limited population size, and class C (several Mb and longer) as recent parental relatedness.

**Class-specific ROH frequency.** At SNP $k$, among $N$ sampled individuals, let $n_x$ carry a class-$x$ run covering $k$ and $n_{x'}$ carry a run of one of the other two classes covering $k$. The class-$x$ ROH frequency is

$$p_x = \frac{n_x}{N - n_{x'}},$$

left undefined when $n_{x'} = N$; the frequency of runs of any class is $p_{\mathrm{all}} = n_{\mathrm{all}}/N$.

## Remarks

The length of an autozygous segment inherited from a common ancestor $g$ generations back on each side is approximately exponential with mean $1/(2g)$ Morgans, so runs from recent, intermediate and ancient ancestry differ in typical length by orders of magnitude and a small mixture separates them; the three-component model was the only one among two to ten components that gave disjoint length intervals in every population studied. Taking the midpoint between the largest member of one class and the smallest member of the next gives a single hard threshold per boundary consistent with the mixture assignment. In the frequency $p_x$ the denominator removes individuals whose genome at $k$ is already covered by a run of another class, since such individuals cannot carry a class-$x$ run there; $p_x$ is thus the conditional frequency of class-$x$ runs among individuals eligible to carry one.

## Depends on

- [LOD score of autozygosity for calling runs of homozygosity](lod-score-of-autozygosity-for-calling-runs-of-homozygosity.md)

## Sources

- T. J. Pemberton, D. Absher, M. W. Feldman, R. M. Myers, N. A. Rosenberg and J. Z. Li, "Genomic Patterns of Homozygosity in Worldwide Human Populations", *American Journal of Human Genetics* 91 (2012), 275–292, Material and Methods (three-component Gaussian classification of ROH lengths and Equations 1–2), <https://doi.org/10.1016/j.ajhg.2012.06.014> (PMC3415543).
