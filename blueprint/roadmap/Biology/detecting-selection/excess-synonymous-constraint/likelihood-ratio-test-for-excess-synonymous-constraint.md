# Likelihood ratio test for excess synonymous constraint

Let $A$ be a codon alignment of $N$ sequences over an open reading frame together with a
phylogenetic tree $T$. Fit, by maximum likelihood on the whole alignment, branch lengths and the
parameters of a Muse-Gaut type codon substitution model with equilibrium codon frequencies
estimated by the position-specific nucleotide product (F3x4), the alignment-wide synonymous rate
being normalized to $1$. For a window $W$ of consecutive codons, compare two nested models, which
differ only inside $W$ and share all global parameters:

- the null model, in which the synonymous rate in $W$ is held at the alignment-wide value $1$ and
  only a window-specific nonsynonymous rate is fitted;
- the alternative model, which adds one free parameter, a window-specific synonymous rate $s_W > 0$.

Let $\ell_0$ and $\ell_1$ be their maximized log-likelihoods. Since the models are nested and the
alternative has exactly one extra parameter, the statistic

$$\Lambda_W = 2\,(\ell_1 - \ell_0)$$

is asymptotically $\chi^2$ with one degree of freedom under the null, and the window is called a
synonymous constraint element when $\hat s_W < 1$ and the resulting $p$-value falls below a
threshold corrected for the number of windows tested.

## Depends on

- [Codon as a triple of nucleotides](../../phylogenetics/codon-substitution-models-and-dn-ds/codon.md)
- [Codons differing at exactly one position](../../phylogenetics/codon-substitution-models-and-dn-ds/is-single-change.md)
- [Site likelihood of a phylogenetic tree](../../phylogenetics/felsenstein-s-pruning-algorithm/likelihood.md)

## Remarks

A functional element overlapping a coding region, such as an RNA structure, a splicing signal or a
transcription factor binding site, makes synonymous changes deleterious there, so the local
synonymous rate drops below the genome-wide average while the amino acid sequence is unaffected.
Separating a global fit from a one-parameter local test is what makes the method usable on short,
deeply sampled alignments such as viral genes, where there is not enough data to estimate a full
$61 \times 61$ substitution matrix per window; on simulated alignments with no synonymous rate
variation the $p$-values are approximately uniform, and resolution improves with alignment depth
and total tree length.

## Sources

- R. S. Sealfon, M. F. Lin, I. Jungreis, M. Y. Wolf, M. Kellis, P. C. Sabeti, "FRESCo: finding
  regions of excess synonymous constraint in diverse viruses", Genome Biology 16 (2015) 38,
  <https://doi.org/10.1186/s13059-015-0603-7> (PMC4376164).
