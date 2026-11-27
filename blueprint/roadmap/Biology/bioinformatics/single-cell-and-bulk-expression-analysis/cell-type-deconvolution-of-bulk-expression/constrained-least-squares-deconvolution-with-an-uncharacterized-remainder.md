# Constrained least-squares deconvolution with an uncharacterized remainder

Let $S \in \mathbb{R}_{\ge 0}^{G \times C}$ be a signature matrix of $C$ cell types over the $G$ signature genes present in a sample, and let $m \in \mathbb{R}^{G}$ be the sample's expression on those genes. The deconvolution estimate is any solution of

$$\hat F \in \operatorname*{arg\,min}_{F \in \Delta} \|S F - m\|_2^2, \qquad \Delta = \Bigl\{F \in \mathbb{R}^{C} : F_c \ge 0 \ (c = 1, \dots, C),\ \sum_{c=1}^{C} F_c \le 1\Bigr\}.$$

1. **Existence and uniqueness.** $\Delta$ is a nonempty compact convex polytope and the objective is a convex quadratic, so a minimizer exists. If $S$ has full column rank $C$, the objective is strictly convex and $\hat F$ is unique.
2. **Remainder.** $f = \sum_c \hat F_c \in [0, 1]$ is the fraction of the signal explained by the modelled cell types, and $1 - f$ is the estimated fraction of uncharacterized ("other") cells.
3. **mRNA-content correction.** Given cell-type mRNA contents $n_c > 0$, set $F'_c = \hat F_c / n_c$ and, when $f' = \sum_c F'_c > 0$,

$$F''_c = \frac{F'_c\, f}{f'} .$$

Then $F''_c \ge 0$, $\sum_c F''_c = f$, so the uncharacterized fraction $1 - f$ is unchanged, and for any two types with $\hat F_d > 0$,

$$\frac{F''_c}{F''_d} = \frac{\hat F_c / n_c}{\hat F_d / n_d},$$

i.e. relative abundances among modelled types are mRNA-fraction ratios divided by mRNA-content ratios.

## Remarks

Allowing $\sum_c F_c < 1$ rather than imposing equality is what lets the model absorb cell populations absent from $S$; without it, the missing signal would be forced onto the modelled types. Items 1 and 2 are standard facts of convex quadratic programming; item 3 is direct algebra, since the rescaling multiplies every $F'_c$ by the same constant $f/f'$. In the quanTIseq implementation, $S$ is a ten-immune-cell signature built from RNA-seq (TPM) profiles, the problem is solved with a least-squares solver under the linear inequality constraints, $n_c$ is taken from the median expression of a housekeeping gene in each immune type, and the remainder is not rescaled because its mRNA content is unknown. Highly collinear signatures (regulatory versus conventional CD4 T cells) make $S$ ill-conditioned; the method handles this with a heuristic re-estimation for low regulatory T-cell fractions, and finally renormalizes all fractions, including the remainder, to sum to one.

## Sources

- F. Finotello, C. Mayer, C. Plattner, et al., "Molecular and pharmacological modulators of the tumor immune contexture revealed by deconvolution of RNA-seq data", Genome Medicine 11 (2019) 34, Methods section "Deconvolution", <https://doi.org/10.1186/s13073-019-0638-6> (PMC6534875).
