# Output of FFT circular convolution

Let $R$ be a field with a star-ring conjugation, let
$n = 2^d$, $\omega \in R$ and $x, y \in R^n$. The vector returned by FFT circular convolution of
$x$ and $y$ with root $\omega$ equals the vector returned by the inverse FFT with root $\omega$
applied to the vector returned by pointwise multiplication of $\hat{x}$ and $\hat{y}$, where
$\hat{x}$ and $\hat{y}$ are the vectors returned by the radix-two FFT of $x$ and of $y$ with
root $\omega$.

Only returned values are compared; operation counts are not.
