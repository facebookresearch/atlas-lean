# Munro-Wild PowerSort source map

This page maps the portions of
[the local paper](munro-wild-powersort.pdf) used by the roadmap. Page numbers
below are printed paper pages and PDF pages; they coincide for this file.

## Node power

Section 3.2.1, Definition 3, page 8 defines the power of the split between two
adjacent runs as the first binary fractional bit at which the two neighboring
run-midpoint positions differ. CPython's `powerloop` is a low-level integer
realization of this idea, but its transcription must be checked against C,
not reconstructed from the paper.

## Merge cost and entropy

Sections 2.2 and 2.3, pages 6-7 define the cost of merging runs of lengths
`m` and `n` to be `m + n`, the length of the untrimmed merge result.  Thus the
cost of a binary merge tree is the sum of its internal-node lengths, equally
`sum_i depth_i * L_i` for leaf lengths `L_i`.  For positive lengths summing to
`N`, the normalized leaf weights are `alpha_i = L_i / N` and their binary
Shannon entropy is `H(alpha) = sum_i alpha_i * log2 (1 / alpha_i)`.

This cost is an abstract accounting measure.  It is not the number of cells
actually moved after `merge_at`'s gallop trimming.  In particular, a logical
merge whose trimming discovers that no directional merge is needed still
contributes the two original run lengths to the paper's merge tree and cost.

## Nearly-optimal search-tree bound

Theorem 1(iii), page 6 states that Method 2 constructs a search tree of cost
`C <= H + 1 + sum_i alpha_i`.  In the all-leaf case used by PowerSort the
weights sum to one, so this is `C <= H + 2`.  Multiplication by the total
length `N` gives the merge-cost term `N * H + 2 * N`.

## Monotonicity and Cartesian-tree interpretation

Section 3.2.1, Lemma 4 and Corollary 5, page 9 state that powers along each
root-to-leaf path strictly increase and identify the resulting tree as the
min-oriented Cartesian tree of node powers. These results motivate the stack
policy. The implementation-facing invariant is stated in CPython's
`Objects/listsort.txt` and discharged against the transcribed `found_new_run`.

## One-pass stack policy

Section 3.2.2, Algorithm 2, page 9 describes the left-to-right stack algorithm:
when a new node power is smaller than a pending power, the completed subtree is
merged; otherwise the open subtree remains on the stack. The paper also bounds
the stack height by the maximum node power.

Algorithm 2 completes the open forest by repeatedly merging the top two runs.
The pinned CPython implementation does not always use that final loop:
`merge_force_collapse` selects the third-last pair when the third-last run is
shorter than the last run.  Therefore the implementation's final tree need not
equal the paper's Cartesian tree.  The alternative is the local rotation
`A + (B + C)` to `(A + B) + C`; under CPython's guard `len A < len C`, its
merge cost decreases by `len C - len A`.  The implementation bridge must prove
cost dominance over the paper tree, not tree equality.

## Optional cost theorem

Theorem 6, pages 9-10 gives PowerSort merge cost at most
`N * H(L_1/N, ..., L_r/N) + 2 * N`, comparisons at most
`N * H(L_1/N, ..., L_r/N) + 3 * N - r`, and logarithmic auxiliary-stack
space.  The optional stretch target transfers only the merge-cost conclusion.
CPython's adaptive run extension and merge routines do not justify importing
the paper's comparison-count argument unchanged, and the project already has
a stronger concrete pending-stack bound.

For the implementation theorem, `L_1, ..., L_r` must be the positive segment
lengths actually pushed by `list_sort_impl` after `count_run` and any
`minrun_next`/`binarysort` extension.  They are not, in general, the maximal
natural-run lengths from the original input and are not necessarily the full
balanced target sequence of CPython's ideal arbitrary-precision minrun
recurrence.  That exact balanced-cycle bridge is itself conditional on the
modeled C exponent being below 32; the implementation's 32-bit mask can depart
from it at larger exponents. A long natural run is consumed at its own length
while advancing the generator only once, and an extension can consume across
a natural-run boundary.  The PowerSort tree bound is length-theoretic and
applies to this actual formed-leaf partition once the implementation policy
bridge is proved; it does not consume exact minrun-cycle equivalence.

## Scope warning

The paper's pseudocode is not the implementation specification. CPython adds
adaptive minrun generation, binary insertion extension, bidirectional stable
merging, galloping, comparator specialization, and concrete finite-width
arithmetic.  It also uses the distinct final-collapse choice described above.
Policy and cost arguments may cite this source; transcription, actual leaf
formation, logical merge events, final-collapse selection, and implementation
safety must cite the pinned CPython sources.
