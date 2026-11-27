# Scale-invariant BFV: leveled FHE without modulus switching

BFV keeps a single ciphertext modulus $q$ throughout evaluation: a homomorphic product is $\mathrm{MultFV}$, which lifts both ciphertexts to centered representatives in $R$, tensors them over the integers, scales by $t/q$ and rounds, reduces modulo $q$, and relinearizes with $\mathrm{RelinFV}$; no modulus switching is applied between levels. This follows Brakerski's scale-invariance principle for LWE-based FHE, in which the plaintext sits in the most significant bits and the tensored ciphertext is scaled down by the plaintext-to-ciphertext modulus ratio ($2/q$ for Brakerski's binary plaintexts, $t/q$ in BFV) before rounding: in Brakerski's scheme the noise grows only linearly in each multiplication ($B\mapsto B\cdot\mathrm{poly}(n)$, rather than $B\mapsto B^{2}\cdot\mathrm{poly}(n)$), and the scheme's properties depend only on the ratio between $q$ and the initial noise level $B$, not on their absolute values.

## Proof sketch

In Brakerski's analysis, write the decryption equation of each input as $\lfloor q/2\rfloor m+v+qk$ for an integer vector $k$ whose norm is bounded in terms of the secret and the dimension. After scaling the tensor product by $2/q$, the large multiples $qk$ contribute terms proportional to $k\,v'$ and $k'\,v$, linear in the input noise, while the term of order $vv'/q$ and the rounding errors are lower order. No term is proportional to $q$, so the growth factor is independent of $q$.

## Depends on

- [BGV and BFV ring ciphertexts](bgv-bfv-ciphertexts.md)

## Proof depends on

- [Ciphertext multiplication by tensoring](tensor-product-multiplication.md)
- [Relinearization by gadget key switching](relinearization.md)

## Sources

- Jean-Claude Bajard, Julien Eynard, M. Anwar Hasan, Vincent Zucca, "A Full RNS Variant of FV Like Somewhat Homomorphic Encryption Schemes", SAC 2016, LNCS 10532 (2017), §§2–4 (`DecFV`, `MultFV`, `RelinFV`), DOI 10.1007/978-3-319-69453-5_23.
- Zvika Brakerski, "Fully Homomorphic Encryption without Modulus Switching from Classical GapSVP", CRYPTO (2012).
