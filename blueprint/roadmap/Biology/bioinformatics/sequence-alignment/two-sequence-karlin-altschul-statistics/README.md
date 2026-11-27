# Two-sequence Karlin–Altschul statistics

## Diagonals of the alignment grid

- [Scores along a diagonal from a given cell](diag-from.md)
- [Scores along the diagonal with a given offset](diag.md)
- [Diagonal offsets of a grid](offsets.md)
- [Length of a diagonal of a grid](diag-len.md)
- [Dropping scores from a diagonal moves its starting cell](drop-diag-from.md)
- [A diagonal from a cell is a suffix of the full diagonal](diag-from-eq-drop-diag.md)
- [Diagonals with offsets outside the grid are empty](diag-eq-nil.md)
- [The diagonal lengths of a grid add up to its number of cells](sum-diag-len.md)
- [A grid with sides at least L has at most 2L diagonals shorter than L](card-filter-diag-len-lt-le.md)

## Ungapped alignment scores and the diagonal decomposition

- [Score of an ungapped alignment with a length bound](align-score.md)
- [Maximal ungapped alignment score of two words](max-align-score.md)
- [The length bound can be cut to the pairs that exist](align-score-eq-min.md)
- [Every ungapped alignment scores at most the maximal alignment score](align-score-le-max-align-score.md)
- [No diagonal segment scores more than the maximal alignment score](max-seg-score-diag-le.md)
- [The maximal ungapped alignment score is attained on a diagonal](exists-max-seg-score-diag-eq.md)
- [For t ≥ 0, maximal alignment score at most t iff no diagonal exceeds t](max-align-score-le-iff.md)
- [A positive level is reached iff some diagonal reaches it](le-max-align-score-iff.md)

## The two-sequence model and the pair-score law

- [Weighted average of a functional over words of a given length](word-expect.md)
- [The two-sequence model: weighted average over pairs of words](two-expect.md)
- [Weighted probability of an event on pairs of words](two-prob.md)
- [Product law of an aligned letter pair](pair-law.md)
- [Score of an aligned letter pair](pair-score.md)
- [The pair-score generating function is the Karlin–Altschul one](score-mgf-pair-law.md)
- [Averaging over a word of length k + n splits at position k](word-expect-append.md)
- [Averaging a function of a word's prefix and suffix](word-expect-take-drop.md)
- [Dropping the first letters of an iid word leaves an iid word](word-expect-drop.md)
- [The score-sequence average is a word average](score-expect-eq-word-expect.md)
- [Letter-by-letter scores of two independent iid words are iid](two-expect-zip-with.md)
- [The scores along one diagonal form an iid pair-score sequence](two-expect-diag.md)
- [Events along one diagonal have their one-sequence probability](two-prob-diag.md)
- [Diagonals reading disjoint sets of letters are independent](two-prob-diag-and-diag-of-disjoint.md)

## The Karlin–Altschul E-value bound

- [Karlin–Altschul upper bound for two sequences](two-prob-le-max-align-score-le.md)

## Elementary symmetric sums and the Bonferroni sieve

- [Elementary symmetric sum](elem-symm.md)
- [Splitting one index off an elementary symmetric sum](elem-symm-succ-erase.md)
- [Double counting for elementary symmetric sums](succ-mul-elem-symm-succ.md)
- [Error bounds in a Newton-type recursion for elementary symmetric sums](elem-symm-recursion-bounds.md)
- [Poisson limit of elementary symmetric sums of uniformly small terms](tendsto-elem-symm.md)
- [Partial alternating sums of binomial coefficients](sum-range-neg-one-pow-mul-choose.md)
- [Bonferroni inequality of even order for a count](indicator-le-bonferroni.md)
- [Bonferroni inequality of odd order for a count](bonferroni-le-indicator.md)
- [Binomial coefficient of a count as a count of subsets](choose-card-filter.md)
- [Poisson limit from Bonferroni bounds and factorial moments](tendsto-of-bonferroni.md)

## Exceeding diagonals and cross-diagonal dependence

- [Number of diagonals with a segment scoring above a threshold](exceed-count.md)
- [Probability that a diagonal has a segment scoring above a threshold](exceed-prob.md)
- [Factorial moments of the number of exceeding diagonals](exceed-moment.md)
- [Cross-diagonal dependence coefficient of order k](cross-dep.md)
- [The dependence coefficient as a sum of joint-minus-product terms](cross-dep-eq-sum.md)
- [A diagonal's exceedance probability is a one-sequence tail probability](exceed-prob-eq.md)
- [Exponential bound on a diagonal's exceedance probability](exceed-prob-le.md)
- [Even-order Bonferroni upper bounds for the maximal alignment score](two-prob-max-align-score-le-le.md)
- [Odd-order Bonferroni lower bounds for the maximal alignment score](le-two-prob-max-align-score-le.md)
- [Second-order bounds with the pairwise dependence coefficient](two-prob-max-align-score-le-second-order.md)

## The Gumbel limit, given a one-sequence tail and vanishing dependence

- [One-sequence tail hypothesis for the maximal segment score](one-sequence-tail.md)
- [The exponential factor at a logarithmic threshold](exp-neg-mul-threshold.md)
- [The logarithmic threshold is negligible against the length m](tendsto-threshold-div.md)
- [Finite-size estimate of the expected number of exceeding diagonals](abs-sum-exceed-prob-sub-le.md)
- [Limit of the expected number of diagonals exceeding the threshold](tendsto-sum-exceed-prob.md)
- [Gumbel limit for two sequences when cross-diagonal dependence vanishes](tendsto-two-prob-max-align-score-le.md)

## Lattice-valued scores

- [Lattice point one step past a threshold in the direction of the span](lattice-above.md)
- [Shifting the threshold by h shifts the lattice point by h](lattice-above-add.md)
- [Lattice correction factor of the exponential tail](lattice-corr.md)
- [For a nonzero span h the lattice correction has period h](lattice-corr-add.md)
- [Above a threshold means at least the next lattice point](lt-iff-lattice-above-le.md)
- [For lattice scores, exceeding t means reaching the next lattice point](score-prob-lt-max-seg-score-eq.md)

## Gumbel approximation for lattice scores

- [Lattice one-sequence tail hypothesis for the maximal segment score](one-sequence-lattice-tail.md)
- [The expected number of exceeding diagonals, lattice case](tendsto-sum-exceed-prob-sub-lattice.md)
- [Gumbel approximation with periodic correction for lattice scores](tendsto-two-prob-max-align-score-le-sub.md)
- [Two-sequence lattice bounds on the maximal alignment score](eventually-lattice-bounds.md)

## Related topics

- [Maximal segment score of a random sequence](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/README.md): the maximal segment score of one i.i.d. score sequence, its ladder decomposition and Cramér root; for lattice-valued scores and a positive root θ > 0, the one-sequence tail hypothesis holds only with K = 0.
- [Gumbel limit of the maximal segment score](../../../../Probability/random-walks/gumbel-limit-of-the-maximal-segment-score/README.md): for one score sequence satisfying the Cramér conditions and given a renewal input (a ladder input and the renewal tail of the excursion heights), the Gumbel limit of the maximal segment score for nonlattice scores, and liminf and limsup bounds for lattice scores.
