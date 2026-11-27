# Fast base conversion is exact up to a small multiple of the source modulus

Fast base conversion maps residues modulo $q=q_1\cdots q_k$ to residues modulo new coprime moduli by evaluating the CRT reconstruction sum without reducing it modulo $q$; the result represents $x+\alpha q$ for an unknown integer $\alpha$ whose size is bounded by the number $k$ of moduli.

Use the notation of the RNS representation: pairwise coprime $q_1,\dots,q_k\ge 2$ with product $q$, $q_i^{*}=q/q_i$, $\tilde q_i\equiv(q_i^{*})^{-1}\pmod{q_i}$. Let $\mathcal{B}$ be a finite set of moduli, each coprime to $q$.

1. For an integer $x\in[0,q)$ with residues $x_i=x\bmod q_i$,

$$
\mathrm{FastBconv}(x,q,\mathcal{B})=\Bigl(\sum_{i=1}^{k}|x_i\tilde q_i|_{q_i}\,q_i^{*}\bmod m\Bigr)_{m\in\mathcal{B}}
$$

is the residue vector of $x+\alpha_xq$ modulo the moduli of $\mathcal{B}$, for one integer $\alpha_x\in[0,k-1]$ common to all $m\in\mathcal{B}$.

2. With centered digits, for an integer $x$ with $-q/2\le x<q/2$, the integer $y=\sum_{i=1}^{k}[x_i\tilde q_i]_{q_i}\,q_i^{*}$ satisfies $y=x+qe$ for an integer $e$ with $|y|\le kq/2$ and $|e|\le k/2$; its residues modulo the moduli of $\mathcal{B}$ are the centered conversion $\mathrm{Conv}$.

When all moduli are single words and the constants $\tilde q_i$ and $q_i^{*}\bmod m$ are precomputed, the conversion is a matrix–vector product of words. The unknown multiple of $q$ (a *$q$-overflow*) must be tolerated or removed by the procedure that uses it. Applied coefficientwise it converts elements of $R_q$.

## Depends on

- [Residue number system representation of $R_q$](rns-representation.md)

## Proof depends on

None.

## Expansion

Each term of the unsigned sum lies in $[0,q)$, so the sum lies in $[0,kq)$ and is congruent to $x$ modulo $q$, which places $\alpha_x$ in $[0,k-1]$ (BEHZ §3.1). In the centered case each term lies in $[-q/2,q/2)$, so $-kq/2\le y<kq/2$; with $-q/2\le x<q/2$ this gives $-(k+1)/2<e<(k+1)/2$, and integrality of $e$ gives $|e|\le k/2$ (Cheon et al., §2.3 and Appendix A.1).

## Sources

- Jean-Claude Bajard, Julien Eynard, M. Anwar Hasan, Vincent Zucca, "A Full RNS Variant of FV Like Somewhat Homomorphic Encryption Schemes", Selected Areas in Cryptography (SAC 2016), LNCS 10532 (2017), pp. 423–442, DOI [10.1007/978-3-319-69453-5_23](https://doi.org/10.1007/978-3-319-69453-5_23): §3.1, Eq. (2) (input $x\in[0,q)$, $\alpha_x\in[0,k-1]$); authors' version.
- Jung Hee Cheon, Kyoohyung Han, Andrey Kim, Miran Kim, Yongsoo Song, "A Full RNS Variant of Approximate Homomorphic Encryption", Selected Areas in Cryptography – SAC 2018, LNCS 11349 (2019), pp. 347–368, DOI [10.1007/978-3-030-10970-7_16](https://doi.org/10.1007/978-3-030-10970-7_16): §2.3 and Appendix A.1 (centered conversion, $|a+Q\cdot e|\le(\ell/2)Q$, $e\in[-\ell/2,\ell/2]$); read as the author manuscript PMC8048025.
- Ahmad Al Badawi, Bharadwaj Veeravalli, Chan Fook Mun, Khin Mi Mi Aung, "High-Performance FV Somewhat Homomorphic Encryption on GPUs: An Implementation using CUDA", IACR Transactions on Cryptographic Hardware and Embedded Systems 2018(2), pp. 70–95, DOI [10.46586/tches.v2018.i2.70-95](https://doi.org/10.46586/tches.v2018.i2.70-95): §5.3, Eq. (3).
