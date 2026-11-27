# Approximate modulus reduction in RNS

To divide an integer known modulo $PQ$ by the auxiliary factor $P$ while staying in residues, convert its residue modulo $P$ to the base of $Q$ by centered fast base conversion, subtract, and multiply by $P^{-1}$. The result is within $k/2$ of the exact quotient, where $k$ is the number of factors of $P$.

Let $\mathcal{B}=\{p_0,\dots,p_{k-1}\}$ and $\mathcal{C}=\{q_0,\dots,q_{\ell-1}\}$ be RNS bases with all moduli pairwise coprime and products $P$ and $Q$. Let $\tilde b$ be an integer whose residues modulo all $p_i$ and $q_j$ are known, let $a=[\tilde b]_P$ be the integer with $a\equiv\tilde b\pmod P$ in $[-P/2,P/2)$, and let $\tilde a=\sum_{i}[a\,\hat p_i^{-1}]_{p_i}\hat p_i$ with $\hat p_i=P/p_i$, the integer whose residues modulo $\mathcal{C}$ are $\mathrm{Conv}_{\mathcal{B}\to\mathcal{C}}([\tilde b]_{\mathcal{B}})$. The procedure

$$
\mathrm{ModDown}_{\mathcal{B}\cup\mathcal{C}\to\mathcal{C}}:\quad b^{(j)}=P^{-1}\bigl(\tilde b-\tilde a\bigr)\bmod q_j\qquad(0\le j<\ell)
$$

returns the residues modulo $\mathcal{C}$ of the integer $b=(\tilde b-\tilde a)/P$, and

$$
\Bigl|b-\frac{\tilde b}{P}\Bigr|=\frac{|\tilde a|}{P}\le\frac{k}{2}.
$$

The companion procedure $\mathrm{ModUp}_{\mathcal{C}\to\mathcal{B}\cup\mathcal{C}}$ appends to $[x]_{\mathcal{C}}$ the conversion $\mathrm{Conv}_{\mathcal{C}\to\mathcal{B}}([x]_{\mathcal{C}})$, the residues of an integer $x+Qe$ with $e$ small. $\mathrm{ModDown}$ divides by the whole auxiliary product $P$; it differs from CKKS rescaling, which divides by the last modulus of the current base.

## Depends on

- [Fast base conversion is exact up to a small multiple of the source modulus](fast-base-conversion.md)

## Proof depends on

None.

## Expansion

Cheon et al., Appendix A.1: by the centered form of fast base conversion, $\tilde a\equiv a\equiv\tilde b\pmod P$ and $|\tilde a|\le kP/2$. Hence $\tilde b-\tilde a$ is divisible by $P$, $b$ is an integer, its residue modulo $q_j$ is $P^{-1}(\tilde b-\tilde a)\bmod q_j$, and $|b-\tilde b/P|=|\tilde a|/P\le k/2$.

## Sources

- Jung Hee Cheon, Kyoohyung Han, Andrey Kim, Miran Kim, Yongsoo Song, "A Full RNS Variant of Approximate Homomorphic Encryption", Selected Areas in Cryptography – SAC 2018, LNCS 11349 (2019), pp. 347–368, DOI [10.1007/978-3-030-10970-7_16](https://doi.org/10.1007/978-3-030-10970-7_16): §3.2, Algorithms 1 (ModUp) and 2 (ModDown), and Appendix A.1 (bound $|b-P^{-1}\tilde b|\le k/2$); read as the author manuscript PMC8048025.
