# Known low bits of an (EC)DSA nonce give a linear relation for the key

If the $l$ least significant bits of the nonce of one (EC)DSA signature are known, then $z=(k-k_0)/2^l$ satisfies $0\le z<r/2^l$ and $z\equiv ta-u\pmod r$ for $t,u$ computable from the signature and the leaked bits, so the residue of $ta-u$ modulo $r$ lies in $[0,r/2^l)$.

**Lemma.** Let $r$ be an odd prime, $a$ an (EC)DSA private key modulo $r$, and $(s_1,s_2)$ a signature on a message with integer hash $H(m)$ and nonce $k\in[1,r-1]$, with $s_1,s_2\not\equiv0\pmod r$ and

$$
ks_2\equiv H(m)+as_1\pmod r .
$$

Let $l\ge1$ and let $k_0=k\bmod 2^l$ be known. Then $z=(k-k_0)/2^l$ is an integer with $0\le z<r/2^l$, and

$$
z\equiv ta-u\pmod r,\qquad t=2^{-l}s_1s_2^{-1},\quad u=2^{-l}\bigl(k_0-s_2^{-1}H(m)\bigr),
$$

where $t$ and $u$ are computed modulo $r$ from $s_1,s_2,H(m),k_0$ and $l$. For ECDSA, $s_1$ and $s_2$ are the components $r$ and $s$ of the signature and $a$ is $d$.

## Depends on

- [ECDSA](ecdsa.md)

## Proof depends on

None.

## Expansion

From $k\equiv s_2^{-1}(H(m)+as_1)$ and $k=k_0+2^lz$ one gets $2^lz\equiv s_1s_2^{-1}a+s_2^{-1}H(m)-k_0$, and multiplying by $2^{-l}$ modulo the odd prime $r$ gives the congruence. The bounds follow from $k_0\le k<r$. Galbraith applies such relations from many signatures, as hidden number problem instances, to recover $a$ with lattice reduction; that application is valid only under additional assumptions, namely a conversion of the residue interval $[0,r/2^l)$ into the absolute-error approximation of the hidden number problem and a distribution hypothesis on the multipliers $t$, and it is not part of this lemma. Here $t$ and $u$ are computable from the signature together with the leaked bits $k_0$.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Section 22.3 (the decomposition $k=k_0+2^lz$ with $0\le z<r/2^l$ and the relation $z\equiv ta-u\pmod r$).
