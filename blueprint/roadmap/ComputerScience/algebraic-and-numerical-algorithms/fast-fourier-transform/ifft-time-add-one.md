# Exact operation count of the inverse FFT

Let $R$ be a field with a star ring structure,
let $d$ be a natural number, $N = 2^d$, $\omega \in R$ arbitrary and $x \in R^N$. The number $T$ of
operations charged by the inverse FFT procedure on $x$ with root $\omega$ satisfies
$T + 1 = (7d + 10) \cdot 2^d + 1$, equivalently $T = (7d + 10) \cdot 2^d$.

Beyond the FFT, the two conjugation passes and the scaling pass each charge $3N$ operations and
computing $1/N$ charges one, for $9N + 1$ in total.
