# Exact cost of the radix-two FFT

Let $R$ be a commutative ring. For every natural number
$d$, every $\omega \in R$ and every vector $x \in R^{2^d}$, the radix-two FFT of $x$ with root
$\omega$ costs $T$ charged operations, where $T + 1 = (7d + 1) \cdot 2^d$; that is,
$T = (7d + 1) \cdot 2^d - 1$.

The count includes the charged reads and writes of the even/odd splits and the writes that
initialize each output vector.
