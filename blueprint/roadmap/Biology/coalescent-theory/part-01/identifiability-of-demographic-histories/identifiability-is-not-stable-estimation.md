# Identifiability is not stable estimation

A demographic model can be identifiable (distinct histories give distinct expected site-frequency spectra) while being poorly conditioned, and without a finiteness assumption it need not be identifiable at all. Myers, Fefferman and Patterson constructed two time-rescaled histories, a constant one and $N(1 - 9F(\tau))$ with $F$ oscillating increasingly fast as $\tau \downarrow 0$, with the same expected spectrum; as Bhaskar and Song (2014, Sec. 2.6) explain, their difference has infinitely many sign changes, so the sign-change identifiability theorems do not apply. Within identifiable piecewise families, Terhorst and Song (2015, Theorem 5) show that the minimax risk $E_\eta\int_0^T|\hat\eta(t) - \eta(t)|\,dt$ from $s$ independent segregating sites is at least of order $1/\log s$ over the bounded subfamily $\{\eta \in \mathcal F_{I,J} : \sup_t\eta(t) < M\}$ of their piecewise-constant bottleneck family with $I + J$ epochs, $J$ later epochs of fixed length $\tau_A$ and bottleneck duration $\tau_B$, under the hypotheses $J > 8$ and $T \ge t_{I+J-1} + \tau_A$, with the bottleneck size $\tau_B/\log s$ and the size increment depending on $s$ as in their proof; the family and these conditions are spelled out in [information-theoretic lower bounds for demographic inference](information-theoretic-lower-bounds.md). The target is to keep apart four properties: injectivity of the map from histories to expected spectra, its conditioning (a modulus of continuity of the inverse), consistency and rates of estimators from finite data, and regularized estimation; and to turn the counterexample and the minimax bound into statements of each kind.

## Proof depends on

- [Information-theoretic lower bounds for demographic inference](information-theoretic-lower-bounds.md)

## Expansion

1. The forward map from piecewise histories to expected spectra, and its injectivity, known for piecewise-constant histories.
2. A modulus of continuity of the inverse on a compact class of histories, and explicit pairs of histories with close spectra.
3. Total variation or KL distance between the induced data distributions, and the consequence for the error of any estimator.
4. The role of regularization or prior information, as a separate statement.

## Sources

- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493. <https://arxiv.org/abs/1309.5056>
- J. Terhorst and Y. S. Song, Fundamental limits on the accuracy of demographic inference based on the sample frequency spectrum, Proc. Natl. Acad. Sci. USA 112 (2015), 7677–7682. <https://doi.org/10.1073/pnas.1503717112>
