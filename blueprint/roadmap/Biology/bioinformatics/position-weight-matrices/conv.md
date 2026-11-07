# Convolution filter response at a window

The response of a convolution (cross-correlation) filter `W` of width `w` on the one-hot
encoded sequence `x` at the window starting at `i`:
`∑ k, ∑ b, W k b * oneHot (x (i + k)) b`.
