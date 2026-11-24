# Model correct

Lossless DC load-flow model and its per-line angle error. The DC flow
is `f e = b e * (θ tail - θ head)`, the DC injection is `L_b * θ` for the
full weighted Laplacian, the lossless unit-magnitude AC sending-end real
power is `b e * sin(θ tail - θ head)`, and the two differ by at most
`b e * |θ tail - θ head| ^ 3 / 6` on every branch.
