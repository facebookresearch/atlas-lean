# Key switching with a special modulus in RNS-CKKS

Key switching in full-RNS CKKS uses a special modulus $P$: the switching key encrypts $P\,s_1$ under $s_2$ modulo $PQ$, the input is lifted by ModUp, multiplied by the key, and divided by $P$ with ModDown. The result decrypts under $s_2$ to $d\,s_1$ modulo $Q_\ell$, up to an error in which the key error is divided by $P$.

Let $N$ be a power of two and $R=\mathbb{Z}[X]/(X^N+1)$. Fix the number of levels $L$ and RNS bases $\mathcal{B}=\{p_0,\dots,p_{k-1}\}$ (the special primes) and $\mathcal{C}=\{q_0,\dots,q_L\}$, with all moduli pairwise coprime, $P=\prod_ip_i$, and, for $0\le\ell\le L$, $\mathcal{C}_\ell=\{q_0,\dots,q_\ell\}$, $Q_\ell=\prod_{j\le\ell}q_j$, $\mathcal{D}_\ell=\mathcal{B}\cup\mathcal{C}_\ell$. Let $s_1,s_2\in R$.

- $\mathrm{KSGen}(s_1,s_2)$: sample $a'$ uniform modulo $PQ_L$ (in residues on $\mathcal{D}_L$) and one error $e'\leftarrow\chi_{err}$ used for all residues, and output the residues on $\mathcal{D}_L$ of $\mathrm{swk}=(b',a')$ with $b'\equiv-a's_2+P\,s_1+e'\pmod{PQ_L}$.
- Key switching at level $\ell$ of $d\in R_{Q_\ell}$, given by its residues on $\mathcal{C}_\ell$: let $\tilde d\in R$ be the integer polynomial represented by $\mathrm{ModUp}_{\mathcal{C}_\ell\to\mathcal{D}_\ell}(d)$, namely the centered fast-conversion lift with $\tilde d\equiv d\pmod{Q_\ell}$ and $\|\tilde d\|_\infty\le\tfrac{\ell+1}{2}Q_\ell$; compute the residues on $\mathcal{D}_\ell$ of $(\tilde c_0,\tilde c_1)=\tilde d\cdot\mathrm{swk}$; and output $\hat c_i=\mathrm{ModDown}_{\mathcal{D}_\ell\to\mathcal{C}_\ell}(\tilde c_i)$ for $i=0,1$.

For fixed integer lifts $\tilde c_0,\tilde c_1$ of these residues modulo $PQ_\ell$, ModDown returns the residues modulo $Q_\ell$ of $(\tilde c_i-\tilde a_i)/P$, where $\tilde a_i\equiv\tilde c_i\pmod P$ is the polynomial produced by the centered conversion inside ModDown. Then $\tilde de'-\tilde a_0-\tilde a_1s_2\in PR$, and

$$
\hat c_0+\hat c_1s_2\equiv d\,s_1+\frac{\tilde d\,e'-\tilde a_0-\tilde a_1s_2}{P}\pmod{Q_\ell}.
$$

Adding $(\hat c_0,\hat c_1)$ to the remaining components of a ciphertext gives a ciphertext under $s_2$. In homomorphic multiplication $s_1=s^{2}$ and $s_2=s$ (relinearization); Cheon et al. use switching keys in the same way for the rotation and conjugation keys of the original scheme.

## Depends on

- [Approximate modulus reduction in RNS](../../lattice-and-code-based-cryptography/rns-arithmetic-for-ring-lwe/approximate-modulus-reduction.md)
- [Fast base conversion is exact up to a small multiple of the source modulus](../../lattice-and-code-based-cryptography/rns-arithmetic-for-ring-lwe/fast-base-conversion.md)
- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)

## Proof depends on

None.

## Expansion

Cheon et al., Appendix A.2: the residues of the key on $\mathcal{D}_\ell$ form an encryption of $P\,s_1$ modulo $PQ_\ell$, so $\tilde c_0+\tilde c_1s_2\equiv\tilde d(Ps_1+e')\equiv P\,ds_1+\tilde de'\pmod{PQ_\ell}$, using $P\tilde d\equiv Pd\pmod{PQ_\ell}$. Modulo $P$ this gives $\tilde a_0+\tilde a_1s_2\equiv\tilde c_0+\tilde c_1s_2\equiv\tilde de'$, so the numerator lies in $PR$; subtracting $\tilde a_0+\tilde a_1s_2$ and dividing by $P$ gives the displayed congruence modulo $Q_\ell$.

## Sources

- Jung Hee Cheon, Kyoohyung Han, Andrey Kim, Miran Kim, Yongsoo Song, "A Full RNS Variant of Approximate Homomorphic Encryption", Selected Areas in Cryptography – SAC 2018, LNCS 11349 (2019), pp. 347–368, DOI [10.1007/978-3-030-10970-7_16](https://doi.org/10.1007/978-3-030-10970-7_16): §2.1 (power-of-two $N$, $R=\mathbb{Z}[X]/(X^N+1)$), §4 ($\mathrm{Setup}$ with bases $\mathcal{B}$, $\mathcal{C}_\ell$, $\mathcal{D}_\ell$ for $0\le\ell\le L$; $\mathrm{KSGen}$, $\mathrm{KeyGen}$ and the steps of $\mathrm{Mult}$) and Appendix A.2 (bound $\|\tilde d_2\|_\infty\le\tfrac12(\ell+1)Q_\ell$ and the paragraph "Multiplication"); read as the author manuscript PMC8048025.
