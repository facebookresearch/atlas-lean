# Correctness of EdDSA verification

An honest EdDSA signature satisfies the cofactorless equation $[S]B=R+[h]A$, hence the cofactored verification equation $[2^cS]B=[2^c]R+[2^ch]A$; the cofactorless equation always implies the cofactored one, but not conversely.

**Theorem.** Let EdDSA parameters be fixed, let $(R,S)$ be the signature of $M$ under a secret key with scalar $s$ and public key $A=[s]B$, and let $h=H(R,A,\mathrm{PH}(M))$. Then

$$
[S]B=R+[h]A ,
$$

so $[2^cS]B=[2^c]R+[2^ch]A$ and the verifier accepts. Moreover, for any $A,R\in E$ and $S\in\{0,\dots,L-1\}$, the cofactorless equation implies the cofactored one.

## Depends on

- [EdDSA](eddsa.md)
- [Correctness of a signature scheme](../../../security-games/generic-security-games/correct-4.md)

## Proof depends on

None.

## Expansion

Since $S\equiv r+hs\pmod L$ and $[L]B=(0,1)$, one has $[S]B=[r]B+[h][s]B=R+[h]A$. Multiplying by $2^c$ gives the cofactored equation, and the same multiplication proves the implication for arbitrary $(A,R,S)$. The converse fails on points with a component of order dividing $2^c$: for $A=(0,1)$, $R=(0,-1)$ (of order $2$) and $S=0$, the cofactored equation holds for every $h$ while $[S]B=R+[h]A$ does not. On inputs in the subgroup $\langle B\rangle$ the two equations are equivalent. Correctness uses that decoding is a left inverse of encoding, so the verifier recovers the signer's $R$ and $A$ and recomputes the same $h$.

## Sources

- S. Josefsson and I. Liusvaara, *Edwards-Curve Digital Signature Algorithm (EdDSA)*, RFC 8032, IRTF, 2017, doi:10.17487/RFC8032, Sections 3.3, 3.4 and 5.1.7.
- D. J. Bernstein, S. Josefsson, T. Lange, P. Schwabe and B.-Y. Yang, *EdDSA for more curves*, 2015, <https://ed25519.cr.yp.to/eddsa-20150704.pdf>, "Verification" and "Cofactorless verification".
- D. J. Bernstein, N. Duif, T. Lange, P. Schwabe and B.-Y. Yang, "High-speed high-security signatures", *Journal of Cryptographic Engineering* 2(2):77–89, 2012, doi:10.1007/s13389-012-0027-1; numbering from the authors' version of 2011-09-26, <https://ed25519.cr.yp.to/ed25519-20110926.pdf>, Section 2 (the stronger equation $SB=R+H(R,A,M)A$).
