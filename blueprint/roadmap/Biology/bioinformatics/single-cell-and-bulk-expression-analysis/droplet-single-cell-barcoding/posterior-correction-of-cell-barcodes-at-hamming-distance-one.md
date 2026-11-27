# Posterior correction of cell barcodes at Hamming distance one

Let $W$ be a whitelist of barcodes of length $L$ over $\{A, C, G, T\}$, and let $\pi$ be a prior on $W$ estimated from the overall barcode count distribution (for example, proportional to the number of reads whose barcode matches $w \in W$ exactly). An observed barcode $b$ comes with base qualities $Q_1, \dots, Q_L$, i.e. per-base error probabilities $e_i = 10^{-Q_i/10} \in (0, 1)$. Assume the independent-substitution error model: base $i$ of the true barcode is miscalled with probability $e_i$, independently across positions, and a miscalled base is uniform over the three other letters.

Let $C(b) = \{c \in W : d_H(b, c) = 1\}$ be the whitelisted barcodes at Hamming distance one from $b$, and for $c \in C(b)$ let $i(c)$ be the position where $c$ and $b$ differ. Conditional on $b$ having arisen from a barcode in $C(b)$ by a single error, the posterior is

$$\Pr(c \mid b) = \frac{\pi(c)\, \dfrac{e_{i(c)}}{1 - e_{i(c)}}}{\displaystyle\sum_{c' \in C(b)} \pi(c')\, \dfrac{e_{i(c')}}{1 - e_{i(c')}}}, \qquad c \in C(b).$$

The posterior is defined when some $c \in C(b)$ has $\pi(c) > 0$ (the denominator is then positive, since every $e_i \in (0,1)$); when $C(b)$ is empty or all its candidates have prior mass $0$, $b$ is left uncorrected. Otherwise the correction rule assigns $b$ to $\arg\max_c \Pr(c \mid b)$ when that maximum is at least $0.975$, breaking exact ties by lexical order, and leaves $b$ uncorrected otherwise. In particular, two candidates that differ from $b$ at the same position have posterior ratio equal to their prior ratio, and a low-quality position (large $e_i$) attracts the correction.

UMIs are corrected by a simpler rule: within the same cell barcode and gene, a UMI at Hamming distance one from a UMI with more reads is merged into it, and reads sharing barcode, UMI and gene are counted once.

## Depends on

- [Phred quality score and base-call error probability](../../reads-assembly-and-metagenomics/quality-aware-paired-end-read-merging/phred-quality-score-and-base-call-error-probability.md)

## Remarks

Under the error model, $\Pr(b \mid c) = \frac{e_{i(c)}}{3} \prod_{j \ne i(c)} (1 - e_j) = \frac{1}{3}\, \frac{e_{i(c)}}{1 - e_{i(c)}} \prod_{j=1}^{L} (1 - e_j)$. The factor $\frac13 \prod_j (1 - e_j)$ is common to all candidates and cancels in Bayes' rule, leaving the odds $e_{i}/(1 - e_i)$ at the single mismatched position times the prior. The high threshold makes the rule conservative: an ambiguous barcode with two plausible parents is discarded rather than guessed.

## Sources

- G. X. Y. Zheng et al., "Massively parallel digital transcriptional profiling of single cells", Nature Communications 8 (2017), 14049, Methods (section "Alignment, barcode assignment and UMI counting"), <https://doi.org/10.1038/ncomms14049>, PMCID: PMC5241818.
