# Noiseless sample extraction from TRLWE to TLWE

Let $(\mathbf{a},b)$ be a TRLWE sample of $\mu\in\mathbb{T}_N[X]$ under $\mathbf{s}=(s_1,\dots,s_k)\in\mathbb{B}_N[X]^{k}$ with $s_i=\sum_js_{i,j}X^{j}$. Define $\mathbf{s}'\in\{0,1\}^{kN}$ by listing all coefficients $s_{i,j}$, and $\mathbf{a}'\in\mathbb{T}^{kN}$ by $a'_{(i,j)}=a_{i,0}$ for $j=0$ and $a'_{(i,j)}=-a_{i,N-j}$ for $j\ge 1$. Then $(\mathbf{a}',b_0)$ is a TLWE sample under $\mathbf{s}'$ of the constant coefficient $\mu_0$ of $\mu$, with the same error as the constant coefficient of the TRLWE error.

## Proof sketch

The constant coefficient of $a_is_i$ in $\mathbb{T}[X]/(X^{N}+1)$ is $a_{i,0}s_{i,0}-\sum_{j\ge 1}a_{i,N-j}s_{i,j}$ because $X^{N}=-1$. Hence the constant coefficient of $b-\langle\mathbf{a},\mathbf{s}\rangle$ equals $b_0-\langle\mathbf{a}',\mathbf{s}'\rangle$, which is $\mu_0+e_0$.

## Depends on

- [TLWE and TRLWE samples over the real torus](tlwe-samples.md)

## Sources

- Ilaria Chillotti, Nicolas Gama, Mariya Georgieva, Malika Izabachène, "TFHE: Fast Fully Homomorphic Encryption over the Torus", Journal of Cryptology (2020), IACR ePrint 2018/421.
