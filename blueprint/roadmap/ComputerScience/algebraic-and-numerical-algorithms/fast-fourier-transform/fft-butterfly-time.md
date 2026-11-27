# Cost of one FFT butterfly

Let $R$ be a commutative ring and $m$ a natural number. For every
$\omega \in R$, all vectors $q, r \in R^m$, every current twiddle $w \in R$ and output vector of
length $2m$ over $R$, and every index $k < m$, one butterfly step costs exactly $8$ charged
operations: two reads, four scalar operations and two writes.
