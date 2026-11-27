# Higher-dimensional representations of isogenies of arbitrary degree

Let $\ell\ne p$ be a prime, $\sigma:E_A\to E_2$ an isogeny of supersingular curves of degree $q<\ell^{e}$ with $\gcd(q,\ell)=1$, and write $\ell^{e}-q=a_1^{2}+a_2^{2}+a_3^{2}+a_4^{2}$ (possible by Lagrange's four-square theorem, and computable in probabilistic polynomial time). Let $\alpha\in\mathrm{End}(E_A^{4})$ be the $4\times4$ integer quaternion-multiplication matrix of $(a_1,\dots,a_4)$, an $(\ell^{e}-q)$-isogeny, $\alpha'$ its analogue on $E_2^{4}$, and $\Sigma=\mathrm{Diag}(\sigma,\dots,\sigma):E_A^{4}\to E_2^{4}$. Kani's lemma applied to the $(\ell^{e}-q,q)$-isogeny diamond formed by $\alpha,\alpha'$ and $\Sigma$ gives an $\ell^{e}$-isogeny $F$ of $E_A^{4}\times E_2^{4}$ with $\ker F=\{(\tilde{\alpha}(P),\Sigma(P)):P\in E_A^{4}[\ell^{e}]\}$. Hence $F$ is computable in time polynomial in $e$ (and $\log p$) from the images under $\sigma$ of a basis of $E_A[\ell^{e}]$, and $\sigma$ is a component of $F$, so $F$ is an efficient representation of $\sigma$ whatever the factorization of $q$. When $\ell^{e}-q$ is a sum of two squares, the same construction works on $E_A^{2}\times E_2^{2}$. This represents the given $\sigma$; the torsion images alone need not single out $\sigma$ among isogenies of degree $q$: for $\ell^{e}=2$ and $q=1$, the identity and $-1$ agree on $E[2]$.

## Proof sketch

The endomorphism $\alpha$ satisfies $\tilde{\alpha}\alpha=[a_1^{2}+\dots+a_4^{2}]$ (Zarhin's trick), and it commutes with the diagonal $\Sigma$ in the sense $\Sigma\alpha=\alpha'\Sigma$, so $(\alpha,\Sigma,\alpha',\Sigma)$ is an isogeny diamond with degrees adding up to $\ell^{e}$, which is prime to the characteristic. Kani's lemma gives that $F$ is an $\ell^{e}$-isogeny and, since $\gcd(q,\ell^{e}-q)=\gcd(q,\ell^{e})=1$, describes its kernel. Computing $F$ from its kernel is a chain of $e$ $(\ell,\dots,\ell)$-isogenies in dimension $8$, and evaluating $F$ at a point embedded in the first factor and projecting gives $\sigma$ in a coordinate.

## Depends on

- [Supersingular elliptic curves and isogenies](../supersingular-isogenies-and-quaternion-orders/supersingular-curves.md)

## Proof depends on

- [Kani's lemma: isogeny diamonds give isogenies of abelian surfaces](kani-criterion.md)

## Sources

- Damien Robert, "Breaking SIDH in Polynomial Time", EUROCRYPT (2023), IACR ePrint 2022/1038.
- Pierrick Dartois, Antonin Leroux, Damien Robert, Benjamin Wesolowski, "SQIsignHD: New Dimensions in Cryptography", EUROCRYPT (2024), IACR ePrint 2023/436, §§3.2–3.3.
