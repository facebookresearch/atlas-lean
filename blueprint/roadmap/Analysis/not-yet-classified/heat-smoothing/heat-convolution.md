# Heat Convolution

Gaussian heat convolution of bounded measurable data `g` at time `t`: the convolution of `g`
with the heat kernel `heatKernel (EuclideanSpace ℝ (Fin n)) t`. It is meant for `t > 0`. The
formula is not set to `g` at `t = 0`: for `n > 0` the kernel vanishes there
(`0 ^ (-n / 2) = 0`), so `heatConvolution n g 0 = 0` for every `g`, the constant `1` included.
