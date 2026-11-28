# Dropping the first letters of an iid word leaves an iid word

For a
[probability vector](../../../../Probability/not-yet-classified/is-dist.md)
`p` on a finite alphabet, natural numbers `k` and `n` and a real functional `G` of words, the
[word average](word-expect.md) over words `w` of length `n` of `G` applied to `w` without its
first `k` letters equals the word average of `G` over words of length `n - k`, with truncated
subtraction: for `k ≥ n` both sides are `G` of the empty word. So dropping the first `k` letters
of a word of `n` independent letters with law `p` leaves a word of `n - k` such letters.
