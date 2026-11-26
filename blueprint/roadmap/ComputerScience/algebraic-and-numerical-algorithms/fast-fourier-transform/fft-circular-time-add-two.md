# Exact cost of FFT circular convolution

Let $R$ be a field with a star-ring structure,
let $d$ be a natural number, let $\omega \in R$, and let $x$ and $y$ be vectors of length $2^d$
over $R$. The cost charged by circular convolution of $x$ and $y$ with root $\omega$, plus $2$,
equals $(21d + 16) \cdot 2^d$.

The cost is the sum of the costs of the two forward transforms, the pointwise product and the
inverse transform.
