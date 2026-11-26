# Generalized Singleton bound for list decoding (Shangguan-Tamo)

Let $C \subseteq \Sigma^n$ be a code of rate $R = \log_{|\Sigma|}|C| / n$ and $L \ge 1$ an integer. If $C$ is $(\rho, L)$-list decodable, i.e. every Hamming ball of radius $\rho n$ contains at most $L$ codewords, then

$$
\rho \le \frac{L}{L+1}(1 - R) + o(1) ,
$$

with the exact form $\lfloor \rho n \rfloor \le \frac{L}{L+1}(n - \log_{|\Sigma|}|C| + 1)$ for linear codes. For $L = 1$ this is the Singleton bound.

## Proof sketch

Puncture $C$ on its first $\log_{|\Sigma|}|C| - 1$ coordinates: by pigeonhole $L + 1$ codewords agree there. Split the remaining $n - k + 1$ coordinates into $L + 1$ blocks of nearly equal size and construct a received word that agrees with the $j$-th codeword on all blocks except block $j$, choosing symbols greedily; it is within distance about $\frac{L}{L+1}(n - k + 1)$ of all $L + 1$ codewords.

## Depends on

- [List-decodable code](../list-decoding/is-list-decodable.md)
- [Singleton bound](../bounds-on-code-size/singleton-bound.md)

## Sources

- Chong Shangguan, Itzhak Tamo, "Combinatorial list-decoding of Reed-Solomon codes beyond the Johnson radius", STOC (2020); arXiv:1911.01502.
