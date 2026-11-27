# Small Montgomery reduction of $q$-overflows

After a fast base conversion, an element known modulo the auxiliary moduli carries an unknown multiple of $q$. One extra small modulus $\tilde m$ removes most of it: a correction by a centered multiple of $q$ and an exact division by $\tilde m$ give a representative of norm at most $\tfrac q2(1+\rho)$.

Let $q=q_1\cdots q_k$ be an RNS base, $\mathcal{B}_{sk}$ an auxiliary base and $\tilde m\ge 2$ a modulus, all moduli pairwise coprime. Let $c\in R=\mathbb{Z}[X]/(X^n+1)$, let $u\in R$ with $\|u\|_\infty\le\tau$, and suppose the residues

$$
c''_m=\bigl|[\tilde m c]_q+qu\bigr|_m\qquad(m\in\mathcal{B}_{sk}\cup\{\tilde m\})
$$

are known. The algorithm $\mathrm{SmMRq}_{\tilde m}$ computes $r_{\tilde m}=[-c''_{\tilde m}\,q^{-1}]_{\tilde m}$ and, for each $m\in\mathcal{B}_{sk}$, $c'_m=|(c''_m+q\,r_{\tilde m})\,\tilde m^{-1}|_m$. Let $\rho>0$. If

$$
\tilde m\rho\ge 2\tau+1,
$$

then $(c'_m)_{m\in\mathcal{B}_{sk}}$ are the residues of a polynomial $c'$ with $c'\equiv c\pmod q$ and $\|c'\|_\infty\le\tfrac q2(1+\rho)$. When the algorithm follows a fast base conversion from $q$ of $|\tilde m c|_q$, which returns $|\tilde m c|_q+\alpha q$ with $\alpha$ coefficientwise in $[0,k-1]$, and $|\tilde m c|_q=[\tilde m c]_q+\varepsilon q$ with $\varepsilon$ coefficientwise in $\{0,1\}$, the overflow $u=\alpha+\varepsilon$ has coefficients in $[0,k]$, so $\tau=k$ suffices; the ciphertexts are kept in base $q$ in the Montgomery form $|\tilde m c|_q$, which costs nothing extra in the conversions.

## Depends on

- [Fast base conversion is exact up to a small multiple of the source modulus](fast-base-conversion.md)

## Proof depends on

None.

## Expansion

BEHZ Appendix A.5: the algorithm computes $c'=([\tilde mc]_q+qu+qr_{\tilde m})/\tilde m$, an exact division by the choice of $r_{\tilde m}$, congruent to $c$ modulo $q$ because $\tilde m$ is invertible modulo $q$, and of norm at most $q(\tfrac12+\tau+\tfrac{\tilde m}{2})/\tilde m\le\tfrac q2(1+\rho)$ under the hypothesis. It is a Montgomery-style reduction with respect to $\tilde m$ using a centered correction $r_{\tilde m}$, rather than the nonnegative correction of classical Montgomery reduction.

## Sources

- Jean-Claude Bajard, Julien Eynard, M. Anwar Hasan, Vincent Zucca, "A Full RNS Variant of FV Like Somewhat Homomorphic Encryption Schemes", Selected Areas in Cryptography (SAC 2016), LNCS 10532 (2017), pp. 423–442, DOI [10.1007/978-3-319-69453-5_23](https://doi.org/10.1007/978-3-319-69453-5_23): §4.2, Algorithm 2 ($\mathrm{SmMRq}_{\tilde m}$), Lemma 4 and Eq. (8), proof in Appendix A.5; authors' version.
