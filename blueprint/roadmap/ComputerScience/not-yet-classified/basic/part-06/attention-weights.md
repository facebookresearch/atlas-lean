# Attention Weights

Scaled dot-product attention weights for query token `i`.

Rows of `X` are token vectors. `WQ` and `WK` are the query and key matrices.
There is no positional encoding and no mask. The key dimension `dk` is
nonzero, as required by the usual scaling factor `1 / √dk`.
