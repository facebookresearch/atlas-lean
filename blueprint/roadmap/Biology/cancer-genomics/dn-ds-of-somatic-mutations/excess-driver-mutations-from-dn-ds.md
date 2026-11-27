# Excess driver mutations from dN/dS

In the [Poisson dN/dS model](poisson-dn-ds-model-with-trinucleotide-substitution-rates.md), suppose
negative selection on the genes considered is negligible, so that passenger mutations of impact $k$
accumulate at the neutral expectation and positively selected (driver) mutations add to it. If
$n_k$ mutations of impact $k$ are observed and $\omega_k > 1$, the fraction $f_k$ and number $d_k$ of
them that are drivers are

$$f_k \;=\; \frac{\omega_k - 1}{\omega_k}, \qquad d_k \;=\; f_k\, n_k .$$

If negative selection is not negligible, these are lower bounds on the true fraction and number of
drivers. More generally, in a cohort of samples $j$ with pre-selection non-synonymous burdens
$b_j$ and per-sample ratios $\omega_j$, a single cohort-level dN/dS estimated under a common
substitution model targets the burden-weighted mean

$$\omega_{\mathrm{global}} \;=\; \frac{\sum_j b_j\, \omega_j}{\sum_j b_j}.$$

## Depends on

- [Poisson dN/dS model with trinucleotide substitution rates](poisson-dn-ds-model-with-trinucleotide-substitution-rates.md)

## Proof sketch

The neutral expectation of non-synonymous mutations is $n_k / \omega_k$, so the excess
$n_k - n_k/\omega_k = n_k(\omega_k - 1)/\omega_k$ is attributed to positive selection; passengers
still accumulate in driver genes at the background rate, so not every non-synonymous mutation in a
driver gene is a driver, even when the gene is selected in every patient. Removal of passengers by
negative selection would lower the neutral baseline below $n_k/\omega_k$ and hide part of the excess,
hence the lower bound. Exome-wide ratios are close to $1$ (pancancer $1.059$ for all non-synonymous
substitutions), so the estimate is sensitive to small biases in the mutation model; for that reason
the driver counts per tumour were computed on non-hypermutated samples (fewer than 500 coding
mutations) with a pentanucleotide model.

## Sources

- I. Martincorena, K. M. Raine, M. Gerstung et al., "Universal Patterns of Selection in Cancer and Somatic Tissues", *Cell* 171 (2017), <https://doi.org/10.1016/j.cell.2017.09.042> (PMC5720395), STAR Methods, subsections "Estimating the number of substitutions fixed by positive selection from dN/dS" and "Pentanucleotide model and removal of polymorphic sites", and the cohort-level dN/dS simulations described with Figure S1.
