# Attn

Single-head scaled dot-product attention.

The output row for token `i` is the softmax-weighted sum of the value rows
`Matrix.vecMul (X j) WV`. The key dimension `dk` is nonzero.
