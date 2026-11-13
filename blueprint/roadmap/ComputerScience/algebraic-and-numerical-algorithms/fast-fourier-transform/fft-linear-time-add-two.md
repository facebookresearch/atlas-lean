# Exact cost of FFT linear convolution

Let $R$ be a field with a star-ring structure,
let $d$ be a natural number, let $\omega \in R$, and let $x$ and $y$ be vectors of length $2^d$
over $R$. The cost charged by zero-padded linear convolution of $x$ and $y$ with root $\omega$,
plus $2$, equals $(42d + 80) \cdot 2^d$.

The cost is that of zero padding both inputs to length $2^{d+1}$ plus that of circular
convolution at length $2^{d+1}$.
