# LZ78 encoding

The LZ78 encoding of a finite list $x$ is the list of tokens that
`LZ78.parseEncodeAux [] x (|x| + 1)` returns, one for each phrase of `LZ78.parse x`, with index
`0` for the empty phrase and index `j ≥ 1` for the `j`-th phrase. A last phrase that repeats an
earlier one, which happens exactly when the input ends inside a known phrase, is coded as
`(i, none)`, where `i` is its own index. Every other phrase is coded as `(i, some a)`, where `a`
is its last symbol and `i` is the index of the phrase without `a`, the empty phrase or an earlier
phrase.
