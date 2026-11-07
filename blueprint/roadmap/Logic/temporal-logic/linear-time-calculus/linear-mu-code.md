# Cantor-pairing code of linear μ-calculus formulas

An injective encoding of linear μ-calculus formulas over `ℕ` atoms as
natural numbers, via the Cantor pairing function `Nat.pair`. This is a Nat
code only, not a complexity input encoding: repeated pairing squares the
code at every unary connective, so the binary length of the code of
`next^d (atom 0)` doubles at each `next` and is exponential in `d`.
Complexity statements use `linearMuTokens` / `linearMuDecodeList` instead.
