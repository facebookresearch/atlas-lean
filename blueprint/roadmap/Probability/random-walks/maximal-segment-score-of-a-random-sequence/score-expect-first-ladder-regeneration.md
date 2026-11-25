# Regeneration of the score walk at the first ladder epoch

For real weights `q` and scores `f` on a finite alphabet, natural numbers `k ≤ n` and real
functionals `H` and `G` of score lists, the [weighted average](score-expect.md) over words of length
`n` of `H(first k scores) · G(remaining scores)`, restricted to the words whose first `k` scores
[end at the first strict ascending ladder epoch](is-first-ladder.md), is the product of the
weighted average of `H` restricted to such segments of length `k` and the weighted average of `G`
over words of length `n - k`: `E[H; τ₊ = k] · E[G]`. For a probability vector `q`, on `{τ₊ = k}`
the walk after `τ₊` is a fresh i.i.d. walk, independent of the ladder segment; iterating,
[the first two ladder segments are independent](score-prob-two-ladders.md).
