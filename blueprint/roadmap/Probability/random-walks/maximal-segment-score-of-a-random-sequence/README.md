# Maximal segment score of a random sequence

## Pathwise layer: walk maximum, maximal segment score, Lindley process

- [Maximum of the score walk](walk-max.md)
- [Maximal segment score of a score list](max-seg-score.md)
- [Lindley reflected walk of a score list](lindley.md)
- [Every prefix sum is at most the walk maximum](sum-le-walk-max-of-prefix.md)
- [Some prefix attains the walk maximum](exists-prefix-sum-eq-walk-max.md)
- [Every contiguous run sums to at most the maximal segment score](sum-le-max-seg-score-of-infix.md)
- [Some contiguous run attains the maximal segment score](exists-infix-sum-eq-max-seg-score.md)
- [The maximal segment score is the largest contiguous-run sum](max-seg-score-eq-of-forall.md)
- [Agreement with Kadane's maximum subarray sum](max-seg-score-eq-max-zero.md)
- [With no positive score the maximal segment score is zero](max-seg-score-eq-zero-of-nonpos.md)
- [The maximal segment score is monotone along contiguous runs](max-seg-score-mono.md)
- [Walk maximum of a concatenation](walk-max-append.md)
- [Lindley duality](lindley-eq-walk-max-reverse.md)
- [The Kadane–Lindley recursion](max-seg-score-concat.md)
- [The maximal segment score is the maximum of the reflected walk](max-seg-score-eq-max-lindley.md)

## Ladder epochs

- [Segment ending at the first strict ascending ladder epoch](is-first-ladder.md)
- [Up to the first ladder epoch the walk maximum is the ladder height](walk-max-of-is-first-ladder.md)
- [Ladder decomposition of the walk maximum](walk-max-append-of-is-first-ladder.md)
- [Without a ladder epoch the walk maximum is zero](walk-max-eq-zero-of-forall.md)
- [At most one prefix of a score list ends at its first ladder epoch](eq-of-is-first-ladder-take.md)
- [A positive walk maximum has a first ladder epoch](exists-is-first-ladder-take.md)

## Weighted averages over score sequences

- [Weighted average over the score sequences of a given length](score-expect.md)
- [Weighted probability of an event on score sequences](score-prob.md)
- [Moment generating function of one score](score-mgf.md)
- [First-step decomposition of the weighted average](score-expect-succ.md)
- [The weighted average factors over two consecutive blocks](score-expect-append.md)
- [Splitting a score sequence at a fixed position](score-expect-take-drop.md)

## The Cramér root and the exponential tail

- [Single-score generating function as a pair-score generating function](score-mgf-eq-pair-mgf.md)
- [The Cramér (Karlin–Altschul) root of the score distribution](exists-unique-score-mgf-eq-one.md)
- [Exponential moment of the score sum](score-expect-exp-sum.md)
- [Finite-horizon Cramér–Lundberg bound for the walk maximum](score-prob-le-walk-max-le.md)
- [Karlin–Altschul-type tail bound for the maximal segment score](score-prob-le-max-seg-score-le.md)

## Lindley process, ladder renewal structure

- [Reversing the score sequence does not change the weighted average](score-expect-reverse.md)
- [The reflected walk and the walk maximum have equal tail weights](score-prob-le-lindley.md)
- [Regeneration of the score sequence at a fixed time](score-expect-take-mul-drop.md)
- [Regeneration of the score walk at the first ladder epoch](score-expect-first-ladder-regeneration.md)
- [Events on two consecutive blocks have product weight](score-prob-take-and-drop.md)
- [The first two ladder segments are independent with the same law](score-prob-two-ladders.md)
- [First-ladder decomposition of a high walk maximum](le-walk-max-iff.md)
- [Defective renewal equation for the walk maximum](score-prob-le-walk-max-eq-sum.md)
- [The tilted ladder-height law is defective](sum-score-expect-first-ladder-exp-le-one.md)

## Boundary cases

- [Without positive scores, a positive segment score has weight zero](score-prob-max-seg-score-pos-eq-zero.md)
- [Repeating one letter bounds the probability of a high score sum](pow-le-score-prob-le-sum.md)
- [A possible positive score makes the maximal segment score unbounded](tendsto-score-prob-le-max-seg-score.md)
- [Nondegenerate scores of nonnegative mean give unbounded segment scores](tendsto-score-prob-le-max-seg-score-of-m.md)

## Mean, variance and positive drift

- [Mean of the score sum](score-expect-sum-eq.md)
- [Variance of the score sum](score-expect-sq-sub-eq.md)
- [Chebyshev bound for the score sum](score-prob-sum-lt-le.md)
- [With positive mean score the walk maximum diverges](tendsto-score-prob-le-walk-max-of-mean-p.md)

## Lattice-valued scores

- [A sum of lattice values is a lattice value](exists-int-sum-eq-mul.md)
- [The maximal segment score of a lattice-valued list is a lattice value](exists-int-max-seg-score-eq-mul.md)
- [For lattice scores the tail weight is constant on open lattice cells](score-prob-lt-max-seg-score-eq-of-lattic.md)
- [With lattice scores, the one-sequence tail forces K = 0](eq-zero-of-lattice.md)
- [Lattice scores have no one-sequence tail with K ≠ 0](not-one-sequence-tail-of-lattice.md)

## Related topics

- [Two-sequence Karlin–Altschul statistics](../../../Biology/bioinformatics/sequence-alignment/two-sequence-karlin-altschul-statistics/README.md): ungapped alignment of two independent i.i.d. sequences, whose scores along each diagonal form an i.i.d. score sequence; the Karlin–Altschul E-value bound, and Gumbel limits given two kinds of input: a one-sequence tail of the pair score (a marginal input, with a positive Cramér root and length growth) and the vanishing at every order of the cross-diagonal dependence coefficients (a joint input).
