# Block Frame eq linear Convolution

With FFT size at least `L + M - 1`, every block frame is the full
linear convolution of that block with the kernel, at every natural
offset (the frame tail past `L + M - 1` is zero).
