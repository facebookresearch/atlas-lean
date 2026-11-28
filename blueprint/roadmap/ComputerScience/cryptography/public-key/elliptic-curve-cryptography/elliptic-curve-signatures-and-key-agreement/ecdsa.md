# ECDSA

The elliptic curve digital signature algorithm signs a message hash $e$ with a per-message secret $k$ as $r=\bar x([k]G)\bmod n$, $s=k^{-1}(e+rd)\bmod n$, and verifies by checking that the $x$-coordinate of $[es^{-1}]G+[rs^{-1}]Q$ reduces to $r$ modulo $n$.

This page states the mathematical core of ECDSA as specified in FIPS 186-5; the standard additionally fixes approved curves, hash functions, encodings and nonce generators.

**Domain parameters.** A finite field $\mathbb{F}_q$ with $q$ an odd prime or $q=2^m$ (elements of $\mathbb{F}_{2^m}$ written in a polynomial basis), an elliptic curve $E$ over $\mathbb{F}_q$, a base point $G\in E(\mathbb{F}_q)$ of prime order $n$, and the cofactor $h=\#E(\mathbb{F}_q)/n$; a map $M\mapsto e(M)$ from messages to nonnegative integers, which in the standard takes the leftmost $\min(\mathrm{len}(n),\mathrm{hashlen})$ bits of an approved hash of $M$ as an integer, where $\mathrm{len}(n)$ is the bit length of $n$; and the conversion $x\mapsto\bar x$ from $\mathbb{F}_q$ to $\{0,\dots,q-1\}$ of NIST SP 800-186, Appendix F.1: the least nonnegative representative for $q$ odd prime, and evaluation of the polynomial at $2$ over $\mathbb{Z}$ for $q=2^m$. The same equations can be run over another finite field with some chosen injective conversion, but then they are not an instance of the standard.

**Keys.** The private key is an integer $d\in[1,n-1]$ and the public key is $Q=[d]G$.

**Signing** a message $M$ with private key $d$, given a per-message secret $k\in[1,n-1]$ produced by a nonce generator (FIPS 186-5 specifies random and deterministic generators):

1. compute $e=e(M)$, the point $R=[k]G$ and $r=\bar x_R\bmod n$, where $x_R$ is the affine $x$-coordinate of $R$;
2. compute $s=k^{-1}(e+rd)\bmod n$;
3. if $r=0$ or $s=0$, this $k$ fails (the standard then draws a new random $k$, or, for deterministic $k$, outputs failure); otherwise output $(r,s)$.

**Verification** of $(r,s)$ on $M$ under $Q$:

1. reject unless $r,s\in[1,n-1]$;
2. compute $e=e(M)$, $u=es^{-1}\bmod n$ and $v=rs^{-1}\bmod n$;
3. compute $R_1=[u]G+[v]Q$ and reject if $R_1=O$;
4. accept if and only if $r=\bar x_{R_1}\bmod n$.

The standard requires the domain parameters to be valid and recommends validating $Q$. Galbraith presents the same equations for an arbitrary group of prime order $n$ with a map $F:G\to\mathbb{Z}/n\mathbb{Z}$ in place of $R\mapsto\bar x_R\bmod n$.

## Depends on

- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)

## Proof depends on

None.

## Expansion

The two rejections have different reasons: with $s=0$ the inverse $s^{-1}$ used in verification does not exist, and with $r=0$ the value $s=k^{-1}e$ does not depend on the private key $d$. Correctness is a separate page; unforgeability is not claimed here.

## Sources

- National Institute of Standards and Technology, *Digital Signature Standard (DSS)*, FIPS 186-5, 2023, doi:10.6028/NIST.FIPS.186-5, Sections 6.1–6.4, in particular 6.3 (per-message secret), 6.4.1 (signature generation) and 6.4.2 (signature verification).
- L. Chen, D. Moody, K. Randall, A. Regenscheid and A. Robinson, *Recommendations for Discrete Logarithm-based Cryptography: Elliptic Curve Domain Parameters*, NIST SP 800-186, 2023, doi:10.6028/NIST.SP.800-186, Appendix F.1.
- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Section 22.2.2.
