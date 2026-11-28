# Relinearization with CRT digits

In RNS BFV the CRT residues serve as the digits of the relinearization gadget: pairing the scaled residue vector $\xi_q(c)$ with $P_{\mathrm{RNS},q}(s^{2})$ reconstructs $cs^{2}$ modulo $q$, and since each digit is below a word-size modulus the error added by relinearization is below $\delta B_{err}k2^{\nu}$.

Let $q=q_1\cdots q_k$ be an RNS base with every $q_i<2^{\nu}$, $q_i^{*}=q/q_i$ and $\tilde q_i\equiv(q_i^{*})^{-1}\pmod{q_i}$. Let $n$ be a power of two and $R=\mathbb{Z}[X]/(X^n+1)$, with expansion factor $\delta=n$ (so $\|fg\|_\infty\le\delta\|f\|_\infty\|g\|_\infty$), and let $s\in R$ be the secret key. For $c\in R$ define, coefficientwise,

$$
\xi_q(c)=\bigl(|c\,\tilde q_1|_{q_1},\dots,|c\,\tilde q_k|_{q_k}\bigr)\in R^{k},\qquad P_{\mathrm{RNS},q}(s^{2})=\bigl(|s^{2}q_1^{*}|_q,\dots,|s^{2}q_k^{*}|_q\bigr)\in R^{k}.
$$

Then $\langle\xi_q(c),P_{\mathrm{RNS},q}(s^{2})\rangle\equiv cs^{2}\pmod q$ for every $c\in R$. The RNS relinearization key is

$$
\mathrm{rlk}_{\mathrm{RNS}}=\Bigl(\bigl[P_{\mathrm{RNS},q}(s^{2})-(\vec e+\vec a\,s)\bigr]_q,\ \vec a\Bigr),\qquad \vec a\leftarrow\mathcal{U}(R_q)^{k},\ \vec e\leftarrow\chi_{err}^{k},
$$

with $\chi_{err}$ bounded by $B_{err}>0$, and for every $c\in R$ the error introduced by pairing $\xi_q(c)$ with this key, taken as its centered representative modulo $q$ (coefficients in $[-q/2,q/2)$), satisfies

$$
\Bigl\|\Bigl[\langle\xi_q(c),-(\vec e+\vec a\,s)\rangle+s\,\langle\xi_q(c),\vec a\rangle\Bigr]_q\Bigr\|_\infty<\delta B_{err}k2^{\nu}.
$$

Modulo $q$, this error is added to the inherent noise $v$ of the BFV ciphertext, where $\mathrm{ct}(s)\equiv\Delta[m]_t+v\pmod q$; the sum is an admissible inherent-noise representative of the relinearized ciphertext, not necessarily the centered one. HPS use the equivalent pairing of plain residues $[c]_{q_i}$ with key components built from $[s^{2}\tilde q_iq_i^{*}]_q$, the CRT idempotents times $s^{2}$.

## Depends on

- [Residue number system representation of $R_q$](rns-representation.md)
- [BGV and BFV ring ciphertexts](../../homomorphic-encryption/leveled-packed-fhe-bgv-and-bfv/bgv-bfv-ciphertexts.md)
- [Ciphertext multiplication by tensoring](../../homomorphic-encryption/leveled-packed-fhe-bgv-and-bfv/tensor-product-multiplication.md)

## Proof depends on

None.

## Expansion

BEHZ Lemma 7 follows from the CRT reconstruction $\sum_i|c\tilde q_i|_{q_i}q_i^{*}\equiv c\pmod q$ multiplied by $s^{2}$. For Lemma 8 (Appendix A.10), the expression is congruent modulo $q$ to $-\langle\xi_q(c),\vec e\rangle$, an integer polynomial whose coefficients have absolute value below $\delta B_{err}\sum_iq_i<\delta B_{err}k2^{\nu}$; the centered representative modulo $q$ of an integer is never larger in absolute value than the integer itself. HPS's variant uses $\sum_i[c]_{q_i}\tilde q_iq_i^{*}\equiv c\pmod q$.

## Sources

- Jean-Claude Bajard, Julien Eynard, M. Anwar Hasan, Vincent Zucca, "A Full RNS Variant of FV Like Somewhat Homomorphic Encryption Schemes", Selected Areas in Cryptography (SAC 2016), LNCS 10532 (2017), pp. 423–442, DOI [10.1007/978-3-319-69453-5_23](https://doi.org/10.1007/978-3-319-69453-5_23): §2 ($n$ a power of two, expansion factor $\delta=n$, moduli below $2^{\nu}$), §4.5, Lemma 7, $\mathrm{rlk}_{\mathrm{RNS}}$, Lemma 8, Eq. (16) and Eq. (17), proof in Appendix A.10; authors' version.
- Shai Halevi, Yuriy Polyakov, Victor Shoup, "An Improved RNS Variant of the BFV Homomorphic Encryption Scheme", Topics in Cryptology – CT-RSA 2019, LNCS 11405 (2019), pp. 83–105, DOI [10.1007/978-3-030-12612-4_5](https://doi.org/10.1007/978-3-030-12612-4_5): §3.3 and §4.1 (plain residues with key components $[\tilde q_iq_i^{*}s^{2}-\alpha_is+e_i]_q$); authors' version of December 5, 2018.
- Ahmad Al Badawi, Bharadwaj Veeravalli, Chan Fook Mun, Khin Mi Mi Aung, "High-Performance FV Somewhat Homomorphic Encryption on GPUs: An Implementation using CUDA", IACR Transactions on Cryptographic Hardware and Embedded Systems 2018(2), pp. 70–95, DOI [10.46586/tches.v2018.i2.70-95](https://doi.org/10.46586/tches.v2018.i2.70-95): §5.3 (RNS relinearization).
