# Array linear FFT convolution agrees with the vector version

Let $R$ be a field with
a star-ring structure, let $d$ be a natural number, let $\omega \in R$ be arbitrary, and let
$x, y$ be vectors over $R$ of length $2^d$. Then array zero-padded linear FFT convolution with
root $\omega$, run on the arrays underlying $x$ and $y$, succeeds and returns the array
underlying the output (of length $2^{d+1}$) of vector zero-padded linear FFT convolution of
$x$ and $y$ at size $2^d$ with root $\omega$.
