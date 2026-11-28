# A distortion map decides Diffie–Hellman triples

If $P$ has prime order $r$ and $\psi$ is a distortion map for $P$ and a bilinear pairing $e$, then $([a]P,[b]P,[c]P)$ satisfies $c\equiv ab\pmod r$ exactly when $e([a]P,\psi([b]P))=e(P,\psi([c]P))$, so comparing the two pairing values decides whether a triple is a Diffie–Hellman triple.

Let $E$, $r$, $e:E[r]\times E[r]\to\mu_r$ and $P\in E(\mathbb{F}_q)$ of order $r$ be as in the definition of a distortion map, and let $\psi$ be a distortion map with respect to $E,r,e,P$. **Theorem.** For all integers $a,b,c$,

$$
c\equiv ab\pmod r \iff e([a]P,\psi([b]P))=e(P,\psi([c]P)).
$$

Consequently the test $D$ that, given $([a]P,[b]P,[c]P)$, outputs whether the two pairing values agree accepts exactly the Diffie–Hellman triples ($c\equiv ab$). If $\psi$ and $e$ can be evaluated in time polynomial in the size of the input, $D$ runs in polynomial time.

## Depends on

- [Distortion map](distortion-map.md)

## Proof depends on

None.

## Expansion

Let $\zeta=e(P,\psi(P))$, of order $r$. Since $\psi$ is a homomorphism, $\psi([b]P)=[b]\psi(P)$, and bilinearity gives $e([a]P,[b]\psi(P))=\zeta^{ab}$ and $e(P,[c]\psi(P))=\zeta^c$, which agree iff $ab\equiv c\pmod r$ because $\zeta$ has order $r$. Calculation of the advantage: in the DDH experiment of the [DDH advantage](../../elgamal-encryption/ddh-advantage.md), where the third exponent of a random triple is uniform in $\mathbb{Z}/r\mathbb{Z}$ and independent of $a,b$, the test accepts a real triple with probability $1$ and a random triple with probability exactly $1/r$ (for each $a,b$ just one residue $c$ is accepted), so its DDH advantage in $\langle P\rangle$ is $1-1/r$. This value is specific to that experiment: drawing the third exponent only among invalid residues would give random-side acceptance $0$.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Section 26.5.2 and Definition 26.6.4.
