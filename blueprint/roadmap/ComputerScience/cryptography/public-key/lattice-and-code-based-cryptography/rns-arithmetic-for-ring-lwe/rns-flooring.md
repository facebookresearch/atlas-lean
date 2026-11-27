# Approximate division by the RNS modulus by flooring

In RNS BFV multiplication, the scaled tensor coefficient $\lfloor\tfrac{t}{q}c\rceil$ is produced directly in the auxiliary base: feed $a=t\,c$, subtract a fast conversion of $|a|_q$ and multiply by $q^{-1}$. The result is $\lfloor\tfrac tq c\rceil$ up to an additive error of absolute value at most $k$.

Let $R=\mathbb{Z}[X]/(X^n+1)$ and let $t\ge 2$ be the plaintext modulus. Let $q=q_1\cdots q_k$ be an RNS base and $\mathcal{B}_{sk}$ an auxiliary RNS base, with all moduli of $q$ and $\mathcal{B}_{sk}$ pairwise coprime. For an integer $a$ whose residues modulo every $q_i$ and every $m\in\mathcal{B}_{sk}$ are known, define for each $m\in\mathcal{B}_{sk}$

$$
\mathrm{fastRNSFloor}_q(a,m)=\bigl(a-\mathrm{FastBconv}(|a|_q,q,\{m\})\bigr)\cdot|q^{-1}|_m\bmod m .
$$

For $a\in R$, and for vectors of residues, $\mathrm{fastRNSFloor}_q$ is applied to each integer coefficient, and $\mathrm{fastRNSFloor}_q(a,\mathcal{B}_{sk})$ denotes the vector of its values for all $m\in\mathcal{B}_{sk}$. Write ciphertexts as polynomials in a variable $Y$ over $R$, so that a degree-one ciphertext is $\mathrm{ct}=\mathrm{ct}[0]+\mathrm{ct}[1]Y\in R[Y]$, with $\|\mathrm{ct}\|_\infty=\max_j\|\mathrm{ct}[j]\|_\infty$. Let $\mathrm{ct}'_1,\mathrm{ct}'_2\in R[Y]$ be degree-one ciphertexts, given by the residues of their integer coefficients in $q\cup\mathcal{B}_{sk}$, with $\|\mathrm{ct}'_i\|_\infty\le\tfrac q2(1+\rho)$ for some $\rho>0$, and let $\mathrm{ct}'_\star=\mathrm{ct}'_1\star\mathrm{ct}'_2\in R[Y]$ be their product in $R[Y]$, computed with integer coefficients and negacyclic multiplication in $R$ (no reduction modulo $q$). Fix the coefficientwise rounding $\lfloor z\rceil=\lfloor z+\tfrac12\rfloor$. Then for $j\in\{0,1,2\}$,

$$
\mathrm{fastRNSFloor}_q\bigl(t\,\mathrm{ct}'_\star[j],m\bigr)\equiv\Bigl\lfloor\frac tq\,\mathrm{ct}'_\star[j]\Bigr\rceil+b_j\pmod m\quad\text{for every }m\in\mathcal{B}_{sk},\qquad\|b_j\|_\infty\le k,
$$

with the same integer polynomial $b_j\in R$ for every $m\in\mathcal{B}_{sk}$. Because the moduli of $\mathcal{B}_{sk}$ are pairwise coprime, these residues determine $\lfloor\tfrac tq\mathrm{ct}'_\star[j]\rceil+b_j$ once its coefficients are known to lie in an interval of length less than $\prod_{m\in\mathcal{B}_{sk}}m$, which is how BEHZ size the auxiliary base.

## Depends on

- [Fast base conversion is exact up to a small multiple of the source modulus](fast-base-conversion.md)
- [BGV and BFV ring ciphertexts](../../homomorphic-encryption/leveled-packed-fhe-bgv-and-bfv/bgv-bfv-ciphertexts.md)

## Proof depends on

None.

## Expansion

BEHZ Appendix A.6: coefficientwise, fast base conversion returns the residues of $|a|_q+qu$ with an integer $u\in[0,k-1]$, so $(a-|a|_q-qu)/q=\lfloor a/q\rfloor-u$ exactly, and $\lfloor a/q\rfloor=\lfloor a/q\rceil+\tau$ with $\tau\in\{-1,0\}$ for half-up rounding; with $a=t\,\mathrm{ct}'_\star[j]$ this gives $b_j=\tau-u$, whose coefficients lie in $[-k,0]$. The hypothesis $\|\mathrm{ct}'_i\|_\infty\le\tfrac q2(1+\rho)$ is assumed here; in BEHZ's multiplication it is provided by the small Montgomery reduction applied beforehand.

## Sources

- Jean-Claude Bajard, Julien Eynard, M. Anwar Hasan, Vincent Zucca, "A Full RNS Variant of FV Like Somewhat Homomorphic Encryption Schemes", Selected Areas in Cryptography (SAC 2016), LNCS 10532 (2017), pp. 423–442, DOI [10.1007/978-3-319-69453-5_23](https://doi.org/10.1007/978-3-319-69453-5_23): §4.2 (bases pairwise coprime), §4.3 (definition of $\mathrm{fastRNSFloor}_q$, Eq. (9) and Lemma 5, Eq. (10)), proof in Appendix A.6; authors' version.
