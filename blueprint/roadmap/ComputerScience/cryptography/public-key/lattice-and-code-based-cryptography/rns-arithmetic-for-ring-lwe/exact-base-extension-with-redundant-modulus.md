# Exact base extension with a redundant modulus

One extra modulus $m_{sk}$ removes the unknown overflow of a fast base conversion exactly: the overflow count is recovered as a centered residue modulo $m_{sk}$. This works for negative inputs and for inputs of absolute value strictly below $\lambda M$.

Let $\mathcal{B}=\{m_1,\dots,m_\ell\}$ be an RNS base with product $M$, and let $m_{sk}\ge 2$ be a modulus with $\gcd(m_{sk},M)=1$. Let $\lambda\ge 1$ be real and let $x$ be an integer with $|x|<\lambda M$ whose residues modulo $m_1,\dots,m_\ell$ and $x_{sk}=|x|_{m_{sk}}$ are known. The residues of $x$ in $\mathcal{B}$ are those of the canonical representative $|x|_M\in[0,M)$, so the fast-base-conversion sum

$$
S=\sum_{i=1}^{\ell}\Bigl|x\,\Bigl(\frac{M}{m_i}\Bigr)^{-1}\Bigr|_{m_i}\frac{M}{m_i}
$$

is the integer whose residues modulo any target modulus coprime to $M$ are returned by $\mathrm{FastBconv}(|x|_M,\mathcal{B},\cdot)$. Put

$$
\alpha_{sk,x}=\Bigl[\bigl(S-x_{sk}\bigr)\,M^{-1}\Bigr]_{m_{sk}}\in\Bigl[-\frac{m_{sk}}{2},\frac{m_{sk}}{2}\Bigr),
$$

computed from the residue of $S$ modulo $m_{sk}$. If $m_{sk}\ge 2(\ell+\lceil\lambda\rceil)$, then the integer identity

$$
S-\alpha_{sk,x}M=x
$$

holds. Consequently, for every modulus $p\ge 2$, reducing $S-\alpha_{sk,x}M$ modulo $p$ returns $x\bmod p$ exactly. When $p$ is coprime to $M$, an admissible target of fast base conversion, this reduction is the procedure $\mathrm{FastBconvSK}(x,\mathcal{B}\cup\{m_{sk}\},\{p\})=(\mathrm{FastBconv}(|x|_M,\mathcal{B},\{p\})-\alpha_{sk,x}M)\bmod p$ of BEHZ, Eq. (13), with fast base conversion applied to the residues of $x$ in $\mathcal{B}$, that is, to the canonical representative $|x|_M$.

The classical Shenoy–Kumaresan extension is a different correction for nonnegative inputs: for $0\le x<M$ it uses the nonnegative residue $\alpha=|(S-x_{sk})M^{-1}|_{m_{sk}}$, and then $S-\alpha M=x$ whenever $m_{sk}>\ell$.

## Depends on

- [Fast base conversion is exact up to a small multiple of the source modulus](fast-base-conversion.md)

## Proof depends on

None.

## Expansion

BEHZ Appendix A.8: $|x|_M=x+\mu M$ with an integer $\mu\in[-\lfloor\lambda\rfloor,\lceil\lambda\rceil]$, and fast conversion gives $S=|x|_M+\alpha' M$ with $0\le\alpha'\le\ell-1$. Hence $(S-x_{sk})M^{-1}\equiv\alpha'+\mu\pmod{m_{sk}}$, and $\alpha'+\mu$ lies in $[-m_{sk}/2,m_{sk}/2)$ under the hypothesis on $m_{sk}$, so the centered residue equals $\alpha'+\mu$ and $S-(\alpha'+\mu)M=x$. In the classical case $\mu=0$ and $\alpha'\in[0,\ell-1]$ is recovered as a nonnegative residue when $m_{sk}>\ell$.

## Sources

- Jean-Claude Bajard, Julien Eynard, M. Anwar Hasan, Vincent Zucca, "A Full RNS Variant of FV Like Somewhat Homomorphic Encryption Schemes", Selected Areas in Cryptography (SAC 2016), LNCS 10532 (2017), pp. 423–442, DOI [10.1007/978-3-319-69453-5_23](https://doi.org/10.1007/978-3-319-69453-5_23): §4.4, Lemma 6 (hypotheses $\lambda\ge 1$, $m_{sk}\ge 2(|\mathcal{B}|+\lceil\lambda\rceil)$) and Eqs. (12)–(13), proof in Appendix A.8 (including the classical nonnegative case with $m_{sk}>\ell$); authors' version.
- A. P. Shenoy, R. Kumaresan, "Fast base extension using a redundant modulus in RNS", IEEE Transactions on Computers 38(2) (1989), 292–297 (original reference for the case $0\le x<M$).
