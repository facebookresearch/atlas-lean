# Truncation to input length fails

The tail is needed: for any positive FFT size `Q`, any block length, a signal of length `N ≥ 1` and a kernel of length `M ≥ 2`, truncating the overlap-add output to the input length loses the final linear coefficients for some signal and kernel.
