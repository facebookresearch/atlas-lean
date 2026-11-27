# Phred quality score and base-call error probability

A Phred quality score $Q \in \mathbb{Z}_{\ge 0}$ attached to a base call encodes the probability $e \in (0,1]$ that the call is wrong through

$$Q = -10 \log_{10} e, \qquad e = 10^{-Q/10}.$$

So $Q = 10, 20, 30, 40$ correspond to error probabilities $10^{-1}, 10^{-2}, 10^{-3}, 10^{-4}$, and each increase of $10$ in $Q$ divides the error probability by $10$. In FASTQ files the score is stored as the single character with code $Q + 33$ (the Sanger encoding, used by Illumina CASAVA 1.8 and later). The map $e \mapsto Q$ is strictly decreasing, and for independent calls the log-probability that all are correct is $\sum_i \log(1 - 10^{-Q_i/10})$.

## Remarks

The logarithmic scale was introduced for capillary sequencing so that error probabilities spanning several orders of magnitude fit in small integers. Earlier Illumina pipelines used a different, odds-based score $Q = -10\log_{10}\bigl(e/(1-e)\bigr)$ with an offset of $64$; the two scales agree to within rounding for $Q \gtrsim 10$. Merging and error-correction tools convert $Q$ back to $e$ before combining evidence from overlapping reads.

## Sources

- J. Zhang, K. Kobert, T. Flouri, A. Stamatakis, "PEAR: a fast and accurate Illumina Paired-End reAd mergeR", Bioinformatics 30(5) (2014) 614-620, Section 2.1. <https://doi.org/10.1093/bioinformatics/btt593> (PMC3933873)
- P. J. A. Cock, C. J. Fields, N. Goto, M. L. Heuer, P. M. Rice, "The Sanger FASTQ file format for sequences with quality scores, and the Solexa/Illumina FASTQ variants", Nucleic Acids Research 38(6) (2010) 1767-1771. <https://doi.org/10.1093/nar/gkp1137>
