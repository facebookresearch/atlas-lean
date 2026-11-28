# Fuzzy extractor and secure sketch

Let $(\mathcal{M}, \mathrm{dis})$ be a metric space and $t \ge 0$. A *fuzzy extractor* $(\mathrm{Gen}, \mathrm{Rep})$ maps a reading $w$ to a key $r$ and public helper $p$, such that $\mathrm{Rep}(w', p) = r$ whenever $\mathrm{dis}(w, w') \le t$ (perfect correctness, as in Dodis, Ostrovsky, Reyzin and Smith). A fuzzy extractor *with error* $\delta$ only requires, for all $w, w'$ with $\mathrm{dis}(w, w') \le t$, that $\mathrm{Rep}(w', p) = r$ with probability at least $1 - \delta$ over the coins of $\mathrm{Gen}$ and $\mathrm{Rep}$ (Fuller, Meng and Reyzin, Definitions 2.1 and 2.2); error $0$ is perfect correctness. It is *(computationally) secure* for a family $\mathcal{W}$ of sources if for every $W \in \mathcal{W}$, $(r, p)$ is (computationally) indistinguishable from $(U, p)$. A *secure sketch* $(\mathrm{SS}, \mathrm{Rec})$ outputs $p = \mathrm{SS}(w)$ with $\mathrm{Rec}(w', p) = w$ for close $w'$, such that $w$ retains high conditional min-entropy given $p$; extracting from $w$ with a strong extractor turns a secure sketch into a fuzzy extractor.

## Depends on

- [Conditional guessing probability and min-entropy](../conditional-guessing-probability-and-min-entropy.md)
- [Leftover hash lemma](../leftover-hash-lemma.md)

## Sources

- Y. Dodis, R. Ostrovsky, L. Reyzin and A. Smith, "Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data", SIAM Journal on Computing 38(1), 2008.
- B. Fuller, X. Meng and L. Reyzin, "Computational Fuzzy Extractors", Information and Computation 275, 2020, Definitions 2.1 and 2.2.
