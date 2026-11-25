# FFT linear convolution

Let $R$ be a field that is a star ring, $d$ a natural number,
$\omega \in R$, and $x, y$ vectors of length $2^d$ over $R$. Linear convolution zero-pads $x$ and
$y$ to length $2^{d+1}$ and returns the FFT circular convolution of the two padded vectors at
length $2^{d+1}$ with root $\omega$. Its cost is the cost of the two paddings plus the cost of
the circular convolution.

The root $\omega$ is used for the padded length $2^{d+1}$, twice the input length.
