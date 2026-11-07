# Fuelled parser for linear μ-calculus token lists

Fuelled parsing of a `linearMuTokens` token list back to a formula,
returning the formula and the unconsumed suffix. The fuel bounds the
recursion depth; `linearMuDecodeList` supplies fuel `l.length + 1`, which
exceeds the token length of every formula encoded in `l`.
