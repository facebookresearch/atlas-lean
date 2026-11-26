# Relinearization by gadget key switching

Let $T\ge 2$ and $\ell=\lceil\log_Tq\rceil$. A relinearization key consists of ring-LWE encryptions $\mathrm{rlk}_i=(-a_is+te_i+T^{i}s^{2},\,a_i)$ for $0\le i<\ell$. Given a three-component ciphertext $(d_0,d_1,d_2)$, write $d_2=\sum_iT^{i}d_{2,i}$ with $\|d_{2,i}\|_\infty< T$ and output $(d_0+\sum_id_{2,i}\mathrm{rlk}_{i,0},\;d_1+\sum_id_{2,i}\mathrm{rlk}_{i,1})$. This is a two-component ciphertext of the same message whose noise increases additively by at most $t\,\ell\,\delta_R\,T\max_i\|e_i\|_\infty$. Security of the key requires a circular-security-type assumption (encryptions of $s^{2}$ under $s$).

## Proof sketch

The added terms decrypt to $\sum_id_{2,i}(T^{i}s^{2}+te_i)=d_2s^{2}+t\sum_id_{2,i}e_i$, so the new two-component ciphertext decrypts to $d_0+d_1s+d_2s^{2}$ plus $t\sum_id_{2,i}e_i$, whose norm is bounded by $t\,\ell\,\delta_R\,T\max_i\|e_i\|_\infty$.

## Depends on

- [BGV and BFV ring ciphertexts](bgv-bfv-ciphertexts.md)

## Proof depends on

- [Ciphertext multiplication by tensoring](tensor-product-multiplication.md)

## Sources

- Zvika Brakerski, Craig Gentry, Vinod Vaikuntanathan, "(Leveled) Fully Homomorphic Encryption without Bootstrapping", ITCS (2012), IACR ePrint 2011/277.
- Junfeng Fan, Frederik Vercauteren, "Somewhat Practical Fully Homomorphic Encryption", IACR ePrint 2012/144 (2012).
