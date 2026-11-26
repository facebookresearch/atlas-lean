# The descent binomial polynomial

For `n,d : ℕ`, write `P_(n,d)(X) = (1/n!) ∏ j=0,...,n-1, (X+j-d)` in `ℚ[X]`, with the empty
product equal to `1`. `descentBinomialPolynomial n d` is this rational polynomial,
equivalently the rising Pochhammer polynomial at `X-d` multiplied by `1/n!`.
