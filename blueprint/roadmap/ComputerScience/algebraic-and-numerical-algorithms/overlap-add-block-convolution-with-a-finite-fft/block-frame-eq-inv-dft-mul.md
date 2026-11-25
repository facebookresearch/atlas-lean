# Block Frame eq inv DFT mul

For a positive FFT size `Q` and an offset `t < Q`, the frame value at `t` is the inverse length-`Q` DFT of the product of the length-`Q` DFTs of the zero-padded block and the zero-padded kernel.
