# EdDSA

EdDSA is a deterministic Schnorr-type signature scheme on a twisted Edwards curve: with secret scalar $s$, public key $A=[s]B$ and nonce $r$ derived by hashing, a signature on $M$ is the encoding of $R=[r]B$ followed by that of $S=(r+hs)\bmod L$, where $h$ hashes the encodings of $R$, $A$ and the prehashed message.

This page states the generic scheme of RFC 8032, Section 3, with one hash function $H$ used for key expansion, nonce derivation and challenges. The named instances refine $H$ (RFC 8032, Section 5): plain Ed25519 is the generic scheme with $H=$ SHA-512, while Ed25519ctx and Ed25519ph prefix the nonce and challenge hash inputs with a nonempty string $\mathrm{dom2}(F,C)$; for Ed448, key expansion is SHAKE256 of the secret key with $114$-octet output, while the nonce and challenge hashes are SHAKE256 of $\mathrm{dom4}(F,C)$ followed by the input.

**Parameters.** An odd prime power $p$; an integer $b$ with $2^{b-1}>p$; an injective $(b-1)$-bit encoding of $\mathbb{F}_p$; a hash function $H$ with $2b$-bit output; $c\in\{2,3\}$; an integer $n$ with $c\le n<b$; a non-square $d\in\mathbb{F}_p$ and a nonzero square $a\in\mathbb{F}_p$; the twisted Edwards curve $E=\{(x,y)\in\mathbb{F}_p^2: ax^2+y^2=1+dx^2y^2\}$ with the twisted Edwards addition law, under which $E$ is a group with neutral element $(0,1)$; a base point $B\ne(0,1)$ of $E$; an odd prime $L$ with $[L]B=(0,1)$ and $2^cL=\#E$; and a prehash function $\mathrm{PH}$ (the identity for PureEdDSA).

**Encodings.** An element $x\in\mathbb{F}_p$ is *negative* if the $(b-1)$-bit encoding of $x$ is lexicographically larger than that of $-x$. $\mathrm{ENC}(x,y)$ is the $(b-1)$-bit encoding of $y$ followed by one bit that is $1$ exactly when $x$ is negative. An integer $S\in\{0,\dots,L-1\}$ is encoded as the $b$-bit little-endian string $\mathrm{ENC}(S)$. *Decoding* a string as a point fails unless the string has exactly $b$ bits and its first $b-1$ bits are the encoding of some $y\in\mathbb{F}_p$; it then sets $w=(y^2-1)/(dy^2-a)$, fails if $w$ is not a square, takes the square root $x$ of $w$ that is negative exactly when the last bit is $1$, fails if $x=0$ and the last bit is $1$, and returns $(x,y)\in E$. Hash outputs are read as little-endian integers in $\{0,\dots,2^{2b}-1\}$.

**Keys.** A secret key is a $b$-bit string $k$. Write $H(k)=(h_0,\dots,h_{2b-1})$, let $s=2^n+\sum_{c\le i<n}2^ih_i$ and $A=[s]B$; the public key is $\mathrm{ENC}(A)$.

**Signing** $M$: let $r=H(h_b\|\cdots\|h_{2b-1}\|\mathrm{PH}(M))$, $R=[r]B$, $h=H(\mathrm{ENC}(R)\|\mathrm{ENC}(A)\|\mathrm{PH}(M))$ and $S=(r+hs)\bmod L$; the signature is the $2b$-bit string $\mathrm{ENC}(R)\|\mathrm{ENC}(S)$.

**Verification** of a $2b$-bit signature on $M$ under a $b$-bit public key: decode the public key as $A\in E$ and the first half of the signature as $R\in E$, read the second half as a little-endian integer $S$, and reject if a decoding fails or $S\ge L$; compute $h=H(\mathrm{ENC}(R)\|\mathrm{ENC}(A)\|\mathrm{PH}(M))$, using the received strings, and accept if and only if

$$
[2^cS]B=[2^c]R+[2^ch]A\quad\text{in }E .
$$

Rejecting $S\ge L$ prevents producing a second valid signature by adding a multiple of $L$ to $S$.

## Depends on

- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)
- [Twisted Edwards curve](../../../../../AlgebraicGeometry/elliptic-curves/edwards-curves-and-complete-addition-laws/twisted-edwards-curve.md)

## Proof depends on

- [The twisted Edwards addition law is complete when $a$ is a square and $d$ is not](../../../../../AlgebraicGeometry/elliptic-curves/edwards-curves-and-complete-addition-laws/twisted-edwards-addition-law-is-complete.md)
- [The Edwards addition law is the group law of an elliptic curve](../../../../../AlgebraicGeometry/elliptic-curves/edwards-curves-and-complete-addition-laws/edwards-addition-agrees-with-the-weierstrass-group-law.md)

## Expansion

That $E$ is a group under the twisted Edwards law: completeness shows the denominators never vanish on $E$, and the substitution $(x,y)\mapsto(\sqrt a\,x,y)$, defined over $\mathbb{F}_p$ because $a$ is a square, carries $E$ with its law to the Edwards curve $\bar x^2+y^2=1+(d/a)\bar x^2y^2$ with coefficient $d/a$, still a non-square; the correspondence theorem with $c=1$ then identifies this law with the chord-and-tangent group law of an elliptic curve. In decoding, $dy^2-a\ne0$ because $dy^2=a$ would make $d=a/y^2$ a square. Decoding is a left inverse of encoding on $E$, and the map $y\mapsto$ its encoding is injective, so the canonical encodings are exactly the strings that decode successfully. If a signer uses the same $r$ for two signatures whose challenges $h_1,h_2$ differ modulo $L$, then $S_1-S_2\equiv(h_1-h_2)s\pmod L$ reveals $s\bmod L$.

## Sources

- S. Josefsson and I. Liusvaara, *Edwards-Curve Digital Signature Algorithm (EdDSA)*, RFC 8032, IRTF, 2017, doi:10.17487/RFC8032, Sections 3 (parameters and group law), 3.1–3.4, 5.1, 5.2 and 8.4.
- D. J. Bernstein, S. Josefsson, T. Lange, P. Schwabe and B.-Y. Yang, *EdDSA for more curves*, 2015, <https://ed25519.cr.yp.to/eddsa-20150704.pdf>, "Encoding and parsing curve points", "Secret keys and public keys", "Signing" and "Verification".
- D. J. Bernstein, N. Duif, T. Lange, P. Schwabe and B.-Y. Yang, "High-speed high-security signatures", *Journal of Cryptographic Engineering* 2(2):77–89, 2012, doi:10.1007/s13389-012-0027-1; numbering from the authors' version of 2011-09-26, <https://ed25519.cr.yp.to/ed25519-20110926.pdf>, Section 2.
