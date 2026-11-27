# Jaccard metric on thresholded PWM models

**Models.** A PWM of width $m$ is a matrix $M = [M(\alpha,i)]$ over the alphabet $\{A,C,G,T\}$; a word $\omega = \omega_1\cdots\omega_m$ scores $S(\omega,M) = \sum_{i=1}^m M(\omega_i, i)$. A threshold $t$ defines the binding-site model (word set) $\Omega(M,t) = \{\omega : S(\omega,M) \ge t\}$, with P-value $P(M,t) = \sum_{\omega\in\Omega(M,t)}P(\omega)$ under an i.i.d. background model.

**Invariances.**
1. Appending zero columns to either end of a PWM changes neither its score distribution nor any P-value.
2. If the background satisfies $p(A) = p(T)$ and $p(C) = p(G)$, the reverse-complement PWM $\tilde M$ ($\tilde M(A,i) = M(T,m-i+1)$, $\tilde M(C,i) = M(G,m-i+1)$, etc.) has the same score distribution and P-values.

**Distance.** Two PWMs of possibly different widths are aligned at a relative shift by padding each with zero columns at positions covered only by the other. For aligned models $\Omega_1,\Omega_2$ define

$$J_1(\Omega_1,\Omega_2) = \frac{P(\Omega_1\cap\Omega_2)}{P(\Omega_1\cup\Omega_2)},$$

the probability that a random word passes both thresholds given that it passes at least one (the ordinary Jaccard index of word sets for a uniform background); padding both aligned PWMs with further zero columns does not change $D_1 = 1 - J_1$. For unaligned models set

$$J_2(\Omega_1,\Omega_2) = \max_{\text{shifts } i}\max\big\{J_1^{(i)}(\Omega_1,\Omega_2),\ J_1^{(i)}(\Omega_1,\tilde\Omega_2)\big\},$$

over all relative shifts and both orientations of the second model.

**Theorem.** $D_2(\Omega_1,\Omega_2) = 1 - J_2(\Omega_1,\Omega_2)$ is a metric on the space of binding-site models given by PWMs with thresholds at fixed P-value levels.

## Depends on

- [P-value of a PWM score threshold](../../position-weight-matrices/p-value.md)

## Expansion

Zero columns add a factor $\sum_\alpha p(\alpha) = 1$ to every word probability and do not change scores, which gives the invariances and lets any finite collection of models be compared at a common width. For fixed alignment, $1 - P(X\cap Y)/P(X\cup Y)$ is the weighted Jaccard (Steinhaus) distance, a metric on measurable sets of positive measure. For the triangle inequality of $D_2$, align $M_1$ and $M_2$ optimally against $M_3$ separately; padding makes the three models live on a common window, where the fixed-alignment triangle inequality applies, and the alignment of $M_1$ with $M_2$ induced through $M_3$ can only be worse than the optimal one. The P-value level, not the raw threshold, is what makes models built from count matrices and from log-odds matrices comparable.

## Sources

- I. E. Vorontsov, I. V. Kulakovskiy, V. J. Makeev, "Jaccard index based similarity measure to compare transcription factor binding site models", Algorithms for Molecular Biology 8 (2013) 23, Algorithm section, Lemmas 1–3 and the Theorem with its proof in the Appendix, <https://doi.org/10.1186/1748-7188-8-23>, PMCID PMC3851813.
