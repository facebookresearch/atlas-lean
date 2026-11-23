# Averaging over a word of length k + n splits at position k

For real weights `p` on a finite alphabet, natural numbers `k` and `n` and a real functional `G`
of words, the [word average](word-expect.md) of `G` over words of length `k + n` equals the
iterated word average of `G(u v)` over words `u` of length `k` and `v` of length `n`, where `u v`
is the concatenation. When `p` is a probability vector this says that a word of `k + n`
independent letters with law `p` is a word of `k` such letters followed by an independent word of
`n` such letters.
