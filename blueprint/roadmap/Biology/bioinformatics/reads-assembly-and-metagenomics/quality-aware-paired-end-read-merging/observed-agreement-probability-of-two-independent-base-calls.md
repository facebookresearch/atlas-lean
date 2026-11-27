# Observed agreement probability of two independent base calls

Let two reads cover the same nucleotide position of a fragment, whose true base is $t \in \{\mathrm{A},\mathrm{C},\mathrm{G},\mathrm{T}\}$. Suppose the calls $X$ and $Y$ are independent given $t$, that $X$ is wrong with probability $e_x$ and $Y$ with probability $e_y$ (from their Phred scores), and that a wrong call is uniformly distributed over the three bases other than $t$. Then

$$\Pr(X = Y) = (1 - e_x)(1 - e_y) + \frac{e_x e_y}{3}, \qquad \Pr(X \ne Y) = e_x + e_y - \frac{4}{3} e_x e_y .$$

Moreover, conditional on observing $X = Y$, the probability that the shared call is the true base is

$$\Pr(X = t \mid X = Y) = \frac{(1 - e_x)(1 - e_y)}{(1 - e_x)(1 - e_y) + e_x e_y / 3}.$$

## Depends on

- [Phred quality score and base-call error probability](phred-quality-score-and-base-call-error-probability.md)

## Proof sketch

Agreement happens either when both calls are correct, with probability $(1-e_x)(1-e_y)$, or when both are wrong and pick the same one of the three wrong bases, with probability $e_x e_y \cdot 3 \cdot (1/3)^2 = e_x e_y/3$; one correct and one wrong call can never agree. The complement gives the mismatch probability, and Bayes' rule gives the conditional statement. Overlap mergers such as PEAR use quality-derived match and mismatch probabilities of this kind to weight a match reward and a mismatch penalty in the score of each candidate overlap and to choose the consensus base in the merged region: a mismatch between two high-quality calls is strong evidence against an overlap, while a mismatch involving a low-quality call is not.

## Sources

- J. Zhang, K. Kobert, T. Flouri, A. Stamatakis, "PEAR: a fast and accurate Illumina Paired-End reAd mergeR", Bioinformatics 30(5) (2014) 614-620, Section 2.1 (overlap algorithm and assembly score). <https://doi.org/10.1093/bioinformatics/btt593> (PMC3933873)
