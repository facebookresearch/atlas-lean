# Full-RNS BFV decryption with a correction modulus

BFV decryption can run entirely on RNS residues. A fast base conversion of $|\gamma t\,\mathrm{ct}(s)|_q$ to the moduli $t$ and $\gamma$ gives the scaled message up to a small error, and the centered residue modulo $\gamma$ cancels that error exactly provided the noise is at most $\tfrac qt(\tfrac12-\tfrac k\gamma)-\tfrac{|q|_t}2$.

Let $R=\mathbb{Z}[x]/(x^n+1)$, let $q=q_1\cdots q_k$ be an RNS base, and let $t\ge 2$ be a plaintext modulus with $\gcd(t,q)=1$. Write $\Delta=\lfloor q/t\rfloor$ and $|q|_t=q\bmod t$, and assume $t|q|_t<q$. Let $\mathrm{ct}=(c_0,c_1)$ be a BFV ciphertext with $\mathrm{ct}(s)=c_0+c_1s\equiv\Delta[m]_t+v\pmod q$, where $[m]_t$ has coefficients in $[-t/2,t/2)$ and $v\in R$ is the inherent noise. Let $\gamma$ be a positive integer with $\gcd(\gamma,t)=\gcd(\gamma,q)=1$ and

$$
\gamma>\frac{2k}{1-t|q|_t/q}.
$$

Algorithm $\mathrm{Dec}_{\mathrm{RNS}}$ computes, for each modulus $u\in\{t,\gamma\}$, $s^{(u)}=\bigl|-\mathrm{FastBconv}(|\gamma t\,\mathrm{ct}(s)|_q,q,\{u\})\cdot|q^{-1}|_u\bigr|_u$, then $\tilde s^{(\gamma)}=[s^{(\gamma)}]_\gamma$, and outputs $\bigl[(s^{(t)}-\tilde s^{(\gamma)})\cdot|\gamma^{-1}|_t\bigr]_t$. If

$$
\|v\|_\infty\le\frac{q}{t}\Bigl(\frac12-\frac{k}{\gamma}\Bigr)-\frac{|q|_t}{2}=\frac{q}{2t}-\frac{|q|_t}{2}-\frac{qk}{t\gamma},
$$

the output equals $[m]_t$. The condition on $\gamma$ makes the right side positive. Since $q/t-\Delta=|q|_t/t$, the bound equals the textbook threshold $(\Delta-|q|_t)/2$ plus $|q|_t/(2t)-qk/(t\gamma)$; BEHZ note that with $\gamma\approx 2^{p+1}k$ it is close to $(\Delta(1-2^{-p})-|q|_t)/2$ for practical parameters. Apart from computing $\mathrm{ct}(s)$ in $R_q$, the algorithm uses $O(kn)$ operations on residues, which are word operations when all moduli are single words.

## Depends on

- [BGV and BFV ring ciphertexts](bgv-bfv-ciphertexts.md)
- [Fast base conversion is exact up to a small multiple of the source modulus](../../lattice-and-code-based-cryptography/rns-arithmetic-for-ring-lwe/fast-base-conversion.md)

## Proof depends on

None.

## Expansion

BEHZ's proof, written with floors only. Let $[\mathrm{ct}(s)]_q=\Delta[m]_t+v+qr$ with $r\in R$, $v_c=tv-[m]_t|q|_t$, and $X=\gamma t[\mathrm{ct}(s)]_q$; since $t\Delta=q-|q|_t$, $X/q=\gamma([m]_t+tr)+\gamma v_c/q$. Fast base conversion of $|X|_q$ returns the residues of $|X|_q+\alpha q$ with an integer polynomial $\alpha$ whose coefficients lie in $[0,k-1]$, and $X$ vanishes modulo $t$ and modulo $\gamma$, so for $u\in\{t,\gamma\}$

$$
s^{(u)}\equiv\frac{X-|X|_q}{q}-\alpha=\Bigl\lfloor\frac Xq\Bigr\rfloor-\alpha=\gamma([m]_t+tr)+\Bigl\lfloor\frac{\gamma v_c}{q}\Bigr\rfloor-\alpha\pmod u
$$

(Appendix A.1, before the passage from floor to rounding). The noise hypothesis gives $\|v_c\|_\infty\le t\|v\|_\infty+|q|_tt/2\le q(\tfrac12-\tfrac k\gamma)$ (Appendix A.3), so each coefficient $w$ of $\gamma v_c/q$ satisfies $|w|\le\gamma/2-k$. With the corresponding coefficient $\alpha_i\in[0,k-1]$ of $\alpha$, $\lfloor w\rfloor-\alpha_i\ge\lfloor-\gamma/2\rfloor+k-(k-1)>-\gamma/2$ and $\lfloor w\rfloor-\alpha_i\le\lfloor\gamma/2-k\rfloor<\gamma/2$, for either parity of $\gamma$, so the centered residue modulo $\gamma$ returns $\lfloor\gamma v_c/q\rfloor-\alpha$ exactly (the correction of Lemma 2). Hence $s^{(t)}-\tilde s^{(\gamma)}\equiv\gamma[m]_t\pmod t$, and multiplying by $\gamma^{-1}$ modulo $t$ returns $[m]_t$.

## Sources

- Jean-Claude Bajard, Julien Eynard, M. Anwar Hasan, Vincent Zucca, "A Full RNS Variant of FV Like Somewhat Homomorphic Encryption Schemes", Selected Areas in Cryptography (SAC 2016), LNCS 10532 (2017), pp. 423–442, DOI [10.1007/978-3-319-69453-5_23](https://doi.org/10.1007/978-3-319-69453-5_23): §3.2–3.5, Lemma 1 (Eq. (3)), Lemma 2 (Eq. (4), hypothesis $\gamma\varepsilon\ge k$), Theorem 1 (Eq. (5), stated with $\le$) and Algorithm 1 ($\mathrm{Dec}_{\mathrm{RNS}}$), proofs in Appendix A.1–A.3; authors' version.
- Ahmad Al Badawi, Bharadwaj Veeravalli, Chan Fook Mun, Khin Mi Mi Aung, "High-Performance FV Somewhat Homomorphic Encryption on GPUs: An Implementation using CUDA", IACR Transactions on Cryptographic Hardware and Embedded Systems 2018(2), pp. 70–95, DOI [10.46586/tches.v2018.i2.70-95](https://doi.org/10.46586/tches.v2018.i2.70-95): §5.3, Algorithm 2 ($\mathrm{DecRNS}$).
