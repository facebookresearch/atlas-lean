# Fixed-point numbers encoded in a modular ring

A fixed-point number with $f$ fractional bits and length $k$ is a rational $\tilde x=\bar x\,2^{-f}$ with $\bar x\in\mathbb{Z}_{\langle k\rangle}=\{-2^{k-1}+1,\dots,2^{k-1}-1\}$. Catrina and Saxena encode it as $\bar x\bmod q$ in a prime field with $q>2^k$; SecureML stores values in $\mathbb{Z}_{2^\ell}$ in two's complement.

Let $k>0$, $f\ge0$ and $e=k-f\ge0$. The *fixed-point type* $\mathbb{Q}_{\langle k,f\rangle}=\{\bar x2^{-f}:\bar x\in\mathbb{Z}_{\langle k\rangle}\}$ samples $[-2^{e-1}+2^{-f},\,2^{e-1}-2^{-f}]$ at spacing $2^{-f}$, with $\mathrm{int}_f(\tilde x)=\tilde x2^f$. The field encoding is $\mathrm{fld}(\bar x)=\bar x\bmod q$; it is injective on $\mathbb{Z}_{\langle k\rangle}$, and for $\bar a,\bar b\in\mathbb{Z}_{\langle k\rangle}$ and $\circ\in\{+,-,\cdot\}$, if $\bar a\circ\bar b\in\mathbb{Z}_{\langle k\rangle}$ then it is recovered from $\mathrm{fld}(\bar a)\circ\mathrm{fld}(\bar b)$ by inverting $\mathrm{fld}$ on its image. The source prints this identity in §2.2 without the range condition; the condition is added here so that the inverse on the type is defined, in line with its §3.3 ("if overflow does not occur"). For example $k=4$, $q=17$ and $\bar a=\bar b=7$ give $49\equiv15=\mathrm{fld}(-2)\pmod{17}$, so inverting $\mathrm{fld}$ on its image returns $-2$, not $49$. A product of two values of type $\mathbb{Q}_{\langle k,f\rangle}$ has resolution $2^{-2f}$ and is converted back to scale $2^{-f}$ by $\mathrm{trunc}(\bar x,f)=\bar x/2^f-\delta_t$, where $\delta_t=\bar x/2^f-\mathrm{trunc}(\bar x,f)$ (exact minus rescaled): rounding down gives $0\le\delta_t<1$ and rounding to nearest (ties down) gives $-1/2<\delta_t\le1/2$. The rescaled integer may still lie outside $\mathbb{Z}_{\langle k\rangle}$; that overflow is a separate range condition, not part of the scale conversion. In SecureML's ring convention a negative $z$ is stored as $2^\ell-|z|$ and its truncation by $\ell_D$ bits is $(2^\ell-\lfloor|z|/2^{\ell_D}\rfloor)\bmod2^\ell$, which rounds toward zero, unlike an arithmetic right shift.

## Depends on

None.

## Proof depends on

None.

## Expansion

A definition. Truncation of secret-shared values is treated by [local share truncation](local-share-truncation.md), [probabilistic truncation](probabilistic-truncation-protocol.md) and [exact truncation with a correction term](exact-share-truncation-correction.md).

## Sources

- Octavian Catrina, Amitabh Saxena, "Secure Computation with Fixed-Point Numbers", Financial Cryptography and Data Security 2010, LNCS 6052, DOI 10.1007/978-3-642-14577-3_6, [conference copy](https://ifca.ai/pub/fc10/31_47.pdf), §2.2, §3.1 and §3.3.
- Payman Mohassel, Yupeng Zhang, "SecureML: A System for Scalable Privacy-Preserving Machine Learning", IEEE Symposium on Security and Privacy 2017, DOI 10.1109/SP.2017.12, [conference copy](https://www.ieee-security.org/TC/SP2017/papers/466.pdf), §IV-A ("Arithmetic Operations on Shared Decimal Numbers", PDF p. 7).
