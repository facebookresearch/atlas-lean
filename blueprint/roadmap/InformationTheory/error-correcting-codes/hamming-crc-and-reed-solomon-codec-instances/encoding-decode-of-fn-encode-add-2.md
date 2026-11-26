# Reed–Solomon codec corrects up to ⌊(n − k)/2⌋ errors

For the [Reed–Solomon codec](encoding-3.md) (distinct points $\alpha_1, \dots, \alpha_n$, $k \le n$, a sound and complete key-equation solver for radius $\lfloor (n - k)/2 \rfloor$), every message polynomial $p$ of degree less than $k$ and every error $e \in F^n$ of Hamming weight at most $\lfloor (n - k)/2 \rfloor$, decoding the codeword of $p$ plus $e$ returns $p$. The degree bound matters: for $n = k = 1$ and the point $0$, the polynomials $X$ and $0$ have the same codeword.
