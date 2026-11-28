# Identifiability is not stable estimation

A demographic model can be identifiable (distinct histories give distinct expected site-frequency spectra) while being poorly conditioned, and without a finiteness assumption it need not be identifiable at all: Myers, Fefferman and Patterson constructed two time-rescaled histories, a constant one and $N(1 - 9F(\tau))$ with $F$ oscillating increasingly fast as $\tau \downarrow 0$, with the same expected spectrum. That this pair lies outside the sign-change identifiability theorems is noted in [generalized Descartes rule and sign-change complexity of population size families](../../site-frequency-spectrum-under-variable-populatio/sign-change-complexity-and-demographic-identifiability/generalized-descartes-rule-and-sign-change-complexity.md), and the minimax lower bound of order $1/\log s$ for estimating a size history from $s$ independent segregating sites within an identifiable bottleneck family is [the inverse-logarithmic minimax lower bound for SFS-based size-history estimation](../../site-frequency-spectrum-under-variable-populatio/minimax-limits-of-sfs-based-demographic-inference/inverse-logarithmic-minimax-lower-bound-for-sfs-based-size-history-estimation.md); neither is restated here. The target is to keep apart four properties: injectivity of the map from histories to expected spectra, its conditioning (a modulus of continuity of the inverse), consistency and rates of estimators from finite data, and regularized estimation; and to turn the counterexample and the minimax bound into statements of each kind.

## Proof depends on

- [Inverse-logarithmic minimax lower bound for SFS-based size-history estimation](../../site-frequency-spectrum-under-variable-populatio/minimax-limits-of-sfs-based-demographic-inference/inverse-logarithmic-minimax-lower-bound-for-sfs-based-size-history-estimation.md)

## Expansion

1. The forward map from piecewise histories to expected spectra, and its injectivity, known for piecewise-constant histories.
2. A modulus of continuity of the inverse on a compact class of histories, and explicit pairs of histories with close spectra.
3. Total variation or KL distance between the induced data distributions, and the consequence for the error of any estimator.
4. The role of regularization or prior information, as a separate statement.

## Sources

- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493. <https://arxiv.org/abs/1309.5056>
- J. Terhorst and Y. S. Song, Fundamental limits on the accuracy of demographic inference based on the sample frequency spectrum, Proc. Natl. Acad. Sci. USA 112 (2015), 7677–7682. <https://doi.org/10.1073/pnas.1503717112>
