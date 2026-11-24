# Averaging a function of a word's prefix and suffix

For real weights `p` on a finite alphabet, natural numbers `k ≤ n` and a real function `Φ` of two
words, the [word average](word-expect.md) over words `w` of length `n` of `Φ(w', w'')`, where `w'`
consists of the first `k` letters of `w` and `w''` of the other `n - k`, equals the iterated word
average of `Φ(u, v)` over words `u` of length `k` and `v` of length `n - k`. When `p` is a
probability vector this says that the two pieces of a word of independent letters with law `p` are
independent words of such letters.
