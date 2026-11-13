# Fuelled parser for modal μ-calculus token lists

Fuelled parsing of a `muTokens` token list back to a formula, returning
the formula and the unconsumed suffix. The fuel bounds the recursion depth;
`muDecodeList` supplies fuel `l.length + 1`.
