# FFT linear convolution on arrays

Let $R$ be a field that is a star ring, $\omega \in R$,
and $x, y$ arrays over $R$, where $x$ has length $n$. If $n = 2^d$ for some natural number $d$
and $y$ also has length $n$, the procedure returns the FFT linear convolution of $x$ and $y$
(read as vectors of length $2^d$) with root $\omega$, an array of length $2n$, at the cost of
that convolution. Otherwise it returns no result, at cost $0$.
