# Exact arithmetic right shift of two additive shares

For shares $a_0+a_1\equiv a\pmod{2^\ell}$ and $0<s<\ell$, $(a\gg s)\equiv(a_0\gg s)+(a_1\gg s)+\mathrm{corr}\cdot2^{\ell-s}+\mathbf 1\{a_0^0+a_1^0\ge2^s\}\pmod{2^\ell}$, where $\gg$ is the arithmetic shift of the two's-complement value, $a_b^0=a_b\bmod2^s$ and $\mathrm{corr}\in\{-1,0,1\}$ records signed wrap-around.

Let $L=2^\ell$, let $a_u,a_0,a_1\in\{0,\dots,L-1\}$ be the lifts of $a$ and of the shares, and $a_b=a_b^12^s+a_b^0$ with $0\le a_b^0<2^s$. For $x\in\mathbb{Z}_L$, $x\gg s=\lfloor(x_u-\mathbf 1\{x_u\ge2^{\ell-1}\}L)/2^s\rfloor\bmod L$. With $\mathrm{corr}=-1$ if $a_u\ge2^{\ell-1}$ while $a_0,a_1<2^{\ell-1}$, $\mathrm{corr}=1$ if $a_u<2^{\ell-1}$ while $a_0,a_1\ge2^{\ell-1}$, and $\mathrm{corr}=0$ otherwise,

$$
(a_0\gg s)+(a_1\gg s)+\mathrm{corr}\cdot2^{\ell-s}+\mathbf 1\{a_0^0+a_1^0\ge2^s\}\equiv a\gg s\pmod{2^\ell} .
$$

The identity holds for every pair of shares, with no failure event and no $\pm1$ error, in contrast to [local share truncation](local-share-truncation.md).

## Depends on

None.

## Proof depends on

- [Exact division of two additive shares by a public integer](share-division-correction-theorem.md)

## Expansion

Specialize the division theorem to $n=2^\ell$, $d=2^s$: $n^0=0$, $n^1=2^{\ell-s}$, $B=0$ and $A=a_0^0+a_1^0\in[0,2^{s+1})$, so $1-C=\mathbf 1\{A\ge2^s\}$. The source's Algorithm 5 computes arithmetic shares of $\mathrm{corr}$ from a DReLU call and a $\binom41$-OT, and of the carry by a millionaires' comparison of the low parts followed by a Boolean-to-arithmetic conversion; that protocol and its hybrid security are a separate page.

## Sources

- Deevashwer Rathee, Mayank Rathee, Nishant Kumar, Nishanth Chandran, Divya Gupta, Aseem Rastogi, Rahul Sharma, "CrypTFlow2: Practical 2-Party Secure Inference", ACM CCS 2020, DOI 10.1145/3372297.3417274; numbers and equations from the author-deposited arXiv:2010.06457v1: rendered p. 8, §4.1.1, Corollary 4.2 and Algorithm 5.
