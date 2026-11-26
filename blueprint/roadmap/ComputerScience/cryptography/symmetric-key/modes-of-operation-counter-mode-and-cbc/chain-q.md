# CBC chain as an oracle algorithm

For an additive group `X`, an initial value `iv` and a message `m : Fin n →
X`, `chainQ iv n m` is the oracle computation that queries the block
permutation on `iv + m 0`, then on the previous output plus the next block,
and returns the vector of outputs.
