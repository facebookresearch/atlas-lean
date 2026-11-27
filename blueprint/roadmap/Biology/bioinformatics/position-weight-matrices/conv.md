# Convolution filter response at a window

For a real filter $W$ of width $w$ (one row per letter), a sequence $x = (x_0, x_1, \dots)$ and a position $i$, the response is

$$\mathrm{conv}_W(x, i) = \sum_{k<w} \sum_{b} W_k(b)\, [\,x_{i+k} = b\,],$$

using the [one-hot encoding](one-hot.md).
