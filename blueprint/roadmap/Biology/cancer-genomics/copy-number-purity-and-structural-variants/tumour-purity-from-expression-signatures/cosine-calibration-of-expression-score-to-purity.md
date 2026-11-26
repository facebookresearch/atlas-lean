# Cosine calibration of an expression score to tumour purity

Let $E$ denote the [combined stromal and immune enrichment score](single-sample-gene-set-enrichment-score.md) of a tumour expression profile and let $\pi \in (0, 1]$ be the fraction of malignant cells in the same sample (its purity). Fitting a one-parameter family of the form $\pi = \cos(a + bE)$ by nonlinear least squares to profiles whose purity had been determined independently from allelic copy-number data gives the calibration

$$\hat{\pi}(E) = \cos\big( 0.6049872018 + 0.0001467884 \, E \big).$$

The map $E \mapsto \hat{\pi}(E)$ is strictly decreasing on the range of scores for which its argument lies in $[0, \pi/2]$, that is for $-4121.5 \lesssim E \lesssim 6579.6$, where it takes values in $[0, 1]$; outside that interval the formula leaves the unit interval or stops being monotone and carries no meaning as a purity. At $E = 0$ it returns $\cos(0.60498\ldots) \approx 0.82$, and larger scores, meaning more stromal and immune signal, return smaller purity, as they must.

## Depends on

- [Single-sample gene-set enrichment score](single-sample-gene-set-enrichment-score.md)

## Expansion

The functional form is not derived from a mixture model; it was selected by symbolic regression against purity calls and then refitted by nonlinear least squares, so it should be read as a monotone calibration curve on a bounded range rather than as a structural relation between expression and cell fractions. A linear map of $E$ into an angle followed by a cosine is a convenient way to obtain a smooth, saturating, bounded function: near the middle of its range $\cos$ is close to linear in its argument, while at the ends its derivative vanishes, which matches the compression of purity estimates near $0$ and $1$. Because the constants are fitted to one expression platform and one cohort, a different platform needs its own refit; what is transportable is the shape and the monotonicity, not the two coefficients. The reported concordance between this estimate and copy-number-based purity was a Pearson correlation of about $0.74$, so the curve locates a sample's purity to within a wide interval and does not replace an allelic copy-number estimate.

## Sources

- K. Yoshihara, M. Shahmoradgoli, E. Martínez et al., "Inferring tumour purity and stromal and immune cell admixture from expression data", Nature Communications 4 (2013), 2612, Eq. (1) and Methods ("Prediction of tumour purity"), <https://doi.org/10.1038/ncomms3612>, PMCID PMC3826632.
