# WOTS+ one-time signatures

Let $w = 2^{\lg w}$ (in SLH-DSA $w = 16$), $\mathrm{len}_1 = \lceil 8n/\lg w \rceil$ and $\mathrm{len}_2 = \lfloor \log_w(\mathrm{len}_1 (w-1)) \rfloor + 1$, $\mathrm{len} = \mathrm{len}_1 + \mathrm{len}_2$ (at most $67$ for the standardized $n$). The *chain function* applies the addressed hash $\mathbf{F}$ iteratively: $\mathrm{chain}(X, i, s)$ applies $\mathbf{F}$ for steps $j = i, \dots, i + s - 1$ with hash address $j$, so $\mathrm{chain}(\mathrm{chain}(X, i, s), i+s, t) = \mathrm{chain}(X, i, s+t)$. The secret key is $\mathrm{len}$ pseudorandom values $sk_i$, the public key is $\mathbf{T}_{\mathrm{len}}$ of the chain ends $\mathrm{chain}(sk_i, 0, w-1)$. To sign an $n$-byte digest, write it in base $w$ as $\mathrm{len}_1$ digits $m_i$, append the base-$w$ digits of the checksum $\sum_i (w - 1 - m_i)$, and output $\sigma_i = \mathrm{chain}(sk_i, 0, m_i)$. *Public-key reconstruction* from a signature computes $\mathbf{T}_{\mathrm{len}}$ of $\mathrm{chain}(\sigma_i, m_i, w - 1 - m_i)$, and verification compares it with the public key.

## Depends on

- [SLH-DSA addresses and tweakable hash calls](slh-dsa-addresses-and-hash-calls.md)

## Sources

- National Institute of Standards and Technology, "Stateless Hash-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
- Andreas Hülsing and Mikhail Kudinov, "Recovering the Tight Security Proof of SPHINCS+", Cryptology ePrint Archive, Paper 2022/346, 2022.
