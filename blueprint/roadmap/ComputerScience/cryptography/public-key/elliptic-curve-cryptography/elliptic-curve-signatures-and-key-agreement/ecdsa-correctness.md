# Correctness of ECDSA

Every ECDSA signature output by the signing algorithm is accepted by the verification algorithm, because $[es^{-1}]G+[rs^{-1}][d]G=[k]G$.

**Theorem.** Fix ECDSA domain parameters: $E$ over $\mathbb{F}_q$, $G$ of prime order $n$, the message-to-integer map $e(\cdot)$ and the field-element conversion $x\mapsto\bar x$, shared by signer and verifier. Let $d\in[1,n-1]$ and $Q=[d]G$, and suppose the signing algorithm, run on a message $M$ with per-message secret $k$, outputs $(r,s)$. Then the verification algorithm accepts $(r,s)$ on $M$ under $Q$.

## Depends on

- [ECDSA](ecdsa.md)
- [Correctness of a signature scheme](../../../security-games/generic-security-games/correct-4.md)

## Proof depends on

None.

## Expansion

The signer outputs only $r,s\in[1,n-1]$, so the range check passes, and verification recomputes the same $e$. With $u=es^{-1}$ and $v=rs^{-1}$ modulo $n$,

$$
u+vd\equiv s^{-1}(e+rd)\equiv s^{-1}\,sk\equiv k\pmod n,
$$

because $s\equiv k^{-1}(e+rd)$. Since $G$ has order $n$, $R_1=[u]G+[v][d]G=[u+vd]G=[k]G=R$, which is not $O$ because $0<k<n$. So $R_1$ and $R$ have the same $x$-coordinate and the comparison $r=\bar x_{R_1}\bmod n$ succeeds. The theorem does not assert that signing succeeds for every $k$.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Section 22.2.2 and Exercise 22.2.9.
- National Institute of Standards and Technology, *Digital Signature Standard (DSS)*, FIPS 186-5, 2023, doi:10.6028/NIST.FIPS.186-5, Sections 6.4.1 and 6.4.2.
