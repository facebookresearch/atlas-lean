# LZ78 token

An LZ78 token over a type $A$ is a pair `(i, s)` of a natural number `i` and
an optional symbol `s : Option A`. It stands for the dictionary entry at index `i`, where index
`0` is the empty phrase and index `j ≥ 1` is the `j`-th phrase, followed by the symbol `a` when
`s = some a` and by nothing when `s = none`. `LZ78.encode` emits an index-only token `(i, none)`
only as its last token, when the input ends inside a known phrase; `LZ78.decode` accepts one at
any position.
