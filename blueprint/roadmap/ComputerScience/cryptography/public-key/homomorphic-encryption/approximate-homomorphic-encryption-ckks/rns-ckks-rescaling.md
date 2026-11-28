# Rescaling in RNS-CKKS divides by the last prime

When the CKKS modulus at level $\ell$ is a product $q_0q_1\cdots q_\ell$ of primes close to the scale $\Delta$, rescaling divides by the last prime $q_\ell$: the residues of $\lfloor c/q_\ell\rceil$ are $q_\ell^{-1}(c^{(j)}-[c]_{q_\ell})\bmod q_j$, and using $q_\ell$ instead of $\Delta$ changes the scaled message by a relative error of at most $2^{-\eta}$ when $\Delta/q_\ell$ is within $2^{-\eta}$ of $1$.

Let $N$ be a power of two and let $q_0,\dots,q_L$ be distinct primes with $q_j\equiv 1\pmod{2N}$, hence odd (word-size in the implementation) and $Q_\ell=\prod_{j=0}^{\ell}q_j$. Let $1\le\ell\le L$ and let $c$ be an integer known by its residues $c^{(j)}=c\bmod q_j$, $0\le j\le\ell$; let $[c]_{q_\ell}\in(-q_\ell/2,q_\ell/2]$ be the centered residue determined by $c^{(\ell)}$ (Cheon et al.'s convention; since $q_\ell$ is odd this is also the residue in $[-q_\ell/2,q_\ell/2)$). For $0\le j<\ell$ put

$$
c'^{(j)}=q_\ell^{-1}\bigl(c^{(j)}-[c]_{q_\ell}\bigr)\bmod q_j .
$$

Then $(c'^{(0)},\dots,c'^{(\ell-1)})$ is the RNS representation modulo $Q_{\ell-1}$ of the integer

$$
c'=\frac{c-[c]_{q_\ell}}{q_\ell}=\Bigl\lfloor\frac{c}{q_\ell}\Bigr\rceil ,
$$

where $\lfloor z\rceil$ is the nearest integer, rounding upwards at a tie; ties do not occur since $q_\ell$ is odd. Applied to both components of a level-$\ell$ ciphertext this is the CKKS rescaling by $p=q_\ell$, computed with $O(\ell)$ modular multiplications per coefficient. Cheon et al. call the basis *approximate* for the scale $\Delta>0$ and precision $\eta$ when $\Delta/q_j\in(1-2^{-\eta},1+2^{-\eta})$ for every level $1\le j\le L$. If this ratio condition holds at the selected level $\ell$, then for every real $m$

$$
\Bigl|\frac{m}{q_\ell}-\frac{m}{\Delta}\Bigr|\le 2^{-\eta}\,\Bigl|\frac{m}{\Delta}\Bigr| ,
$$

so the scale drift is a relative error of at most $2^{-\eta}$, separate from the rounding error of rescaling.

## Depends on

- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)
- [CKKS rescaling divides message and error by the scale](ckks-rescaling.md)
- [Residue number system representation of $R_q$](../../lattice-and-code-based-cryptography/rns-arithmetic-for-ring-lwe/rns-representation.md)

## Proof depends on

None.

## Expansion

Cheon et al., Appendix A.2: $c-[c]_{q_\ell}$ is divisible by $q_\ell$, so $c'$ is an integer with residues $q_\ell^{-1}(c^{(j)}-[c]_{q_\ell})\bmod q_j$, and it equals $\lfloor c/q_\ell\rceil$ since $[c]_{q_\ell}/q_\ell\in(-\tfrac12,\tfrac12)$ for odd $q_\ell$. The output ciphertext is the one produced by non-RNS rescaling with $p=q_\ell$, so that procedure's rounding-error bound applies unchanged. The drift bound (§3.1) is $|m/q_\ell-m/\Delta|=|\Delta/q_\ell-1|\,|m/\Delta|$.

## Sources

- Jung Hee Cheon, Kyoohyung Han, Andrey Kim, Miran Kim, Yongsoo Song, "A Full RNS Variant of Approximate Homomorphic Encryption", Selected Areas in Cryptography – SAC 2018, LNCS 11349 (2019), pp. 347–368, DOI [10.1007/978-3-030-10970-7_16](https://doi.org/10.1007/978-3-030-10970-7_16): §2 (residues in $(-q/2,q/2]$, rounding upwards at ties), §3.1 (approximate basis over all levels and the drift bound), §1 (prime moduli $q_\ell\equiv 1\pmod{2N}$), §4 ($\mathrm{RS}$; word-size moduli) and Appendix A.2, paragraph "Rescaling" (identity $c_i'=q_\ell^{-1}(c_i-[c_i]_{q_\ell})=\lfloor q_\ell^{-1}c_i\rceil$); read as the author manuscript PMC8048025.
