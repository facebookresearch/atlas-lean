# Relinearization by gadget key switching

Let $T\ge 2$ and $\ell=\lceil\log_Tq\rceil$. In BGV, whose noise is scaled by $t$, a relinearization key consists of ring-LWE encryptions $\mathrm{rlk}_i=(-a_is+te_i+T^{i}s^{2},\,a_i)$ for $0\le i<\ell$. Given a three-component ciphertext $(d_0,d_1,d_2)$, write $d_2=\sum_iT^{i}d_{2,i}$ with $\|d_{2,i}\|_\infty< T$ and output $(d_0+\sum_id_{2,i}\mathrm{rlk}_{i,0},\;d_1+\sum_id_{2,i}\mathrm{rlk}_{i,1})$. This is a two-component ciphertext of the same message whose noise increases additively by at most $t\,\ell\,\delta_R\,T\max_i\|e_i\|_\infty$. Security of the key requires a circular-security-type assumption (encryptions of $s^{2}$ under $s$). BFV, whose noise is not scaled by $t$, uses the same gadget without the factor $t$: $\mathrm{RelinFV}$ takes the key $\mathrm{rlk}_i=([T^{i}s^{2}-(a_is+e_i)]_q,\,a_i)$ for $0\le i<\ell_{T,q}=\lfloor\log_Tq\rfloor+1$ and maps $(d_0,d_1,d_2)$ to $\bigl([d_0+\sum_id_{2,i}\mathrm{rlk}_{i,0}]_q,\,[d_1+\sum_id_{2,i}\mathrm{rlk}_{i,1}]_q\bigr)$, where $(d_{2,i})_i$ is the radix-$T$ decomposition of $d_2$, so that $\sum_iT^{i}d_{2,i}\equiv d_2\pmod q$.

## Proof sketch

The added terms decrypt to $\sum_id_{2,i}(T^{i}s^{2}+te_i)=d_2s^{2}+t\sum_id_{2,i}e_i$, so the new two-component ciphertext decrypts to $d_0+d_1s+d_2s^{2}$ plus $t\sum_id_{2,i}e_i$, whose norm is bounded by $t\,\ell\,\delta_R\,T\max_i\|e_i\|_\infty$. For the BFV key the added terms decrypt to $\sum_id_{2,i}(T^{i}s^{2}-e_i)\equiv d_2s^{2}-\sum_id_{2,i}e_i\pmod q$, so the noise changes by $-\sum_id_{2,i}e_i$, with no factor $t$.

## Depends on

- [BGV and BFV ring ciphertexts](bgv-bfv-ciphertexts.md)

## Proof depends on

- [Ciphertext multiplication by tensoring](tensor-product-multiplication.md)

## Sources

- Zvika Brakerski, Craig Gentry, Vinod Vaikuntanathan, "(Leveled) Fully Homomorphic Encryption without Bootstrapping", ITCS (2012), IACR ePrint 2011/277.
- Jean-Claude Bajard, Julien Eynard, M. Anwar Hasan, Vincent Zucca, "A Full RNS Variant of FV Like Somewhat Homomorphic Encryption Schemes", SAC 2016, LNCS 10532 (2017), §§2–4 (`DecFV`, `MultFV`, `RelinFV`), DOI 10.1007/978-3-319-69453-5_23.
