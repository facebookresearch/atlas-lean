# Programmable bootstrapping evaluates only negacyclic functions

In $\mathbb{T}_N[X]$, multiplication by $X^{N}$ is negation, so for every test polynomial $v$ and every $\bar{\varphi}\in\mathbb{Z}_{2N}$, the constant coefficient $c(\bar{\varphi})$ of $X^{-\bar{\varphi}}v$ satisfies $c(\bar{\varphi}+N)=-c(\bar{\varphi})$. Conversely, for every function $f:\mathbb{Z}_{2N}\to\mathbb{T}$ with $f(x+N)=-f(x)$ there is a unique $v$ (namely $v_j=f(j)$ for $0\le j< N$) with $c=f$. Consequently, arbitrary functions of the message can be bootstrapped only on half of the torus, which requires a padding bit (messages in $[0,1/2)$) or a multi-bootstrapping technique.

## Proof sketch

The constant coefficient of $X^{-\bar{\varphi}}v$ is $v_{\bar{\varphi}}$ for $0\le\bar{\varphi}< N$ and $-v_{\bar{\varphi}-N}$ for $N\le\bar{\varphi}< 2N$, from $X^{N}=-1$. Choosing the coefficients of $v$ from the values of $f$ on $[0,N)$ realizes any negacyclic $f$, and only those.

## Depends on

- [TLWE and TRLWE samples over the real torus](tlwe-samples.md)

## Proof depends on

- [Blind rotation of a test polynomial by an encrypted phase](blind-rotation.md)
- [Noiseless sample extraction from TRLWE to TLWE](sample-extraction.md)

## Sources

- Ilaria Chillotti, Nicolas Gama, Mariya Georgieva, Malika Izabachène, "TFHE: Fast Fully Homomorphic Encryption over the Torus", Journal of Cryptology (2020), IACR ePrint 2018/421.
