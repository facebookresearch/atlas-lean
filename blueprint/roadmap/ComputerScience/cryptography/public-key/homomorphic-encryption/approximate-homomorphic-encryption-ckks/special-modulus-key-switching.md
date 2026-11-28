# Key switching with a special modulus in RNS-CKKS

Key switching in full-RNS CKKS uses special primes with product $P$: the switching key encrypts $P\,s_1$ under $s_2$ modulo $PQ$; to switch, the component multiplying $s_1$ is lifted by ModUp, multiplied by the key, and both products are divided by $P$ with ModDown. This is the relinearization step of Cheon et al.'s homomorphic multiplication.

Let $N$ be a power of two and $R=\mathbb{Z}[X]/(X^N+1)$. Fix the number of levels $L$ and RNS bases $\mathcal{B}=\{p_0,\dots,p_{k-1}\}$ (the special primes) and $\mathcal{C}=\{q_0,\dots,q_L\}$, with all moduli pairwise coprime, $P=\prod_ip_i$, and, for $0\le\ell\le L$, $\mathcal{C}_\ell=\{q_0,\dots,q_\ell\}$, $Q_\ell=\prod_{j\le\ell}q_j$, $\mathcal{D}_\ell=\mathcal{B}\cup\mathcal{C}_\ell$. Residues and conversions use Cheon et al.'s convention $(-m/2,m/2]$ for centered residues. Let $s_1,s_2\in R$.

- $\mathrm{KSGen}(s_1,s_2)$: sample $(a'^{(0)},\dots,a'^{(k+L)})$ uniformly from $\prod_iR_{p_i}\times\prod_jR_{q_j}$ and one error $e'\leftarrow\chi_{err}$, and output $\mathrm{swk}=(\mathrm{swk}^{(0)},\dots,\mathrm{swk}^{(k+L)})$ with $\mathrm{swk}^{(i)}=(b'^{(i)},a'^{(i)})$, where $b'^{(i)}=-a'^{(i)}s_2+e'\bmod p_i$ for $0\le i<k$ and $b'^{(k+j)}=-a'^{(k+j)}s_2+[P]_{q_j}s_1+e'\bmod q_j$ for $0\le j\le L$. Equivalently, $\mathrm{swk}$ is the RNS representation on $\mathcal{D}_L$ of $(b',a')$ with $b'\equiv-a's_2+P\,s_1+e'\pmod{PQ_L}$.
- Relinearization at level $\ell$ with $\mathrm{evk}=\mathrm{KSGen}(s^{2},s)$: given a level-$\ell$ extended ciphertext $(d_0,d_1,d_2)$ in residues on $\mathcal{C}_\ell$, compute $(\tilde d_2^{(0)},\dots,\tilde d_2^{(k-1)},d_2^{(0)},\dots,d_2^{(\ell)})=\mathrm{ModUp}_{\mathcal{C}_\ell\to\mathcal{D}_\ell}(d_2)$; set $\tilde{\mathrm{ct}}^{(i)}=\tilde d_2^{(i)}\cdot\mathrm{evk}^{(i)}\bmod p_i$ and $\tilde{\mathrm{ct}}^{(k+j)}=d_2^{(j)}\cdot\mathrm{evk}^{(k+j)}\bmod q_j$; apply $\mathrm{ModDown}_{\mathcal{D}_\ell\to\mathcal{C}_\ell}$ to each of the two components of $\tilde{\mathrm{ct}}$, giving $(\hat c_0,\hat c_1)$; and output $\bigl(\hat c_0^{(j)}+d_0^{(j)},\ \hat c_1^{(j)}+d_1^{(j)}\bigr)\bmod q_j$ for $0\le j\le\ell$.

Cheon et al. state that $\mathrm{KSGen}(s_1,s_2)$ generates a key converting a ciphertext under $s_1$ into a ciphertext of the same message under $s_2$, and use such keys also for the rotation and conjugation keys. They analyze the relinearization step in Appendix A.2 under a heuristic error model; the special primes are chosen with $P$ large so that the key-switching error is small.

## Depends on

- [Approximate modulus reduction in RNS](../../lattice-and-code-based-cryptography/rns-arithmetic-for-ring-lwe/approximate-modulus-reduction.md)
- [Fast base conversion is exact up to a small multiple of the source modulus](../../lattice-and-code-based-cryptography/rns-arithmetic-for-ring-lwe/fast-base-conversion.md)
- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)

## Proof depends on

None.

## Expansion

Why the procedure works, as an explanation derived from the definitions (Cheon et al. do not display this general identity). Write $\tilde d_2\in R$ for the integer polynomial represented by the ModUp output, so $\tilde d_2\equiv d_2\pmod{Q_\ell}$ and $\|\tilde d_2\|_\infty\le\tfrac{\ell+1}{2}Q_\ell$ (Appendix A.2). Since the key restricted to $\mathcal{D}_\ell$ encrypts $Ps^{2}$ modulo $PQ_\ell$, fixed integer lifts $\tilde c_0,\tilde c_1$ of the components of $\tilde{\mathrm{ct}}$ satisfy $\tilde c_0+\tilde c_1s\equiv P\,d_2s^{2}+\tilde d_2e'\pmod{PQ_\ell}$. ModDown returns the residues modulo $Q_\ell$ of $(\tilde c_i-\tilde a_i)/P$ with $\tilde a_i\equiv\tilde c_i\pmod P$, and reducing the previous congruence modulo $P$ shows $\tilde d_2e'-\tilde a_0-\tilde a_1s\in PR$. Hence

$$
\hat c_0+\hat c_1s\equiv d_2s^{2}+\frac{\tilde d_2\,e'-\tilde a_0-\tilde a_1s}{P}\pmod{Q_\ell},
$$

so the output decrypts under $s$ like $(d_0,d_1,d_2)$ under $(1,s,s^{2})$, up to an error in which the key error is divided by $P$; this is the quantity Cheon et al. estimate in Appendix A.2 ("$P\cdot\hat{\mathrm{ct}}\approx\tilde{\mathrm{ct}}$").

## Sources

- Jung Hee Cheon, Kyoohyung Han, Andrey Kim, Miran Kim, Yongsoo Song, "A Full RNS Variant of Approximate Homomorphic Encryption", Selected Areas in Cryptography – SAC 2018, LNCS 11349 (2019), pp. 347–368, DOI [10.1007/978-3-030-10970-7_16](https://doi.org/10.1007/978-3-030-10970-7_16): §2 (residues in $(-q/2,q/2]$), §2.1 (power-of-two $N$, $R=\mathbb{Z}[X]/(X^N+1)$), §4 ($\mathrm{Setup}$ with bases $\mathcal{B}$, $\mathcal{C}_\ell$, $\mathcal{D}_\ell$ for $0\le\ell\le L$; $\mathrm{KSGen}$; $\mathrm{KeyGen}$ with $\mathrm{evk}=\mathrm{KSGen}(s^{2},s)$; the steps of $\mathrm{Mult}$) and Appendix A.2 (bound $\|\tilde d_2\|_\infty\le\tfrac12(\ell+1)Q_\ell$ and the paragraph "Multiplication"); read as the author manuscript PMC8048025.
