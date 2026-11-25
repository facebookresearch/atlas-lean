# Overlap Add eq linear Convolution

For block length `L ≥ 1`, kernel length `M ≥ 1` and FFT size `Q ≥ L + M - 1`, overlap-add equals the full linear convolution at every natural index, including the final `M - 1` tail and beyond it.
