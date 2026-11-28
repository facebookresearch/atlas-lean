# A distortion map decides Diffie–Hellman triples

If $P$ has prime order $r$ and $\psi$ is a distortion map for $P$ and a bilinear pairing $e$, then $([a]P,[b]P,[c]P)$ satisfies $c\equiv ab\pmod r$ exactly when $e([a]P,\psi([b]P))=e(P,\psi([c]P))$; the resulting test has DDH advantage $1-1/r$.

Let $E$, $r$, $e:E[r]\times E[r]\to\mu_r$ and $P\in E(\mathbb{F}_q)$ of order $r$ be as in the definition of a distortion map, and let $\psi$ be a distortion map with respect to $E,r,e,P$. **Theorem.** For all integers $a,b,c$,

$$
c\equiv ab\pmod r \iff e([a]P,\psi([b]P))=e(P,\psi([c]P)).
$$

Consequently the distinguisher $D$ that, given $([a]P,[b]P,[c]P)$, outputs whether the two pairing values agree accepts every Diffie–Hellman triple ($c\equiv ab$) and accepts a triple with $c$ uniform in $\mathbb{Z}/r\mathbb{Z}$ and independent of $a,b$ with probability exactly $1/r$; its DDH advantage in $\langle P\rangle$ is $1-1/r$. If $\psi$ and $e$ can be evaluated in time polynomial in the size of the input, $D$ runs in polynomial time.

## Depends on

- [Distortion map](distortion-map.md)
- [Advantage of a DDH distinguisher](../../elgamal-encryption/ddh-advantage.md)

## Proof depends on

None.

## Expansion

Let $\zeta=e(P,\psi(P))$, of order $r$. Since $\psi$ is a homomorphism, $\psi([b]P)=[b]\psi(P)$, and bilinearity gives $e([a]P,[b]\psi(P))=\zeta^{ab}$ and $e(P,[c]\psi(P))=\zeta^c$, which agree iff $ab\equiv c\pmod r$. For $c$ uniform and independent, $\Pr[c\equiv ab]=1/r$.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Section 26.5.2 and Definition 26.6.4.
