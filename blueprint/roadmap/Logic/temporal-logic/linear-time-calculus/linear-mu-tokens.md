# Token-list encoding of linear μ-calculus formulas

A polynomial-size token-list encoding of linear μ-calculus formulas over
`ℕ` atoms, used for the complexity statements in `WantedExt`. Each connective
contributes one tag token (`Nat.pair` of a small tag with `0`), and each atom
or variable contributes one token `Nat.pair tag value`, whose binary size is
`O(log value)`. The canonical bitstring encoding of a `List ℕ` delimits each
token, so the bitstring for a formula has length linear in the number of
connectives plus the total binary size of its atoms: `next^d (atom 0)` is
encoded by exactly `d + 1` tokens, unlike its Cantor-paired `linearMuCode`,
whose binary length is exponential in `d`.
