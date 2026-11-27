# SLH-DSA addresses and tweakable hash calls

SLH-DSA separates every hash call by a 32-byte *address* $\mathrm{ADRS}$ consisting of a layer address, a tree address, an address type (WOTS+ hash, WOTS+ public key, tree, FORS tree, FORS roots, WOTS+ PRF, FORS PRF) and three type-dependent words (key pair, chain or tree height, hash or tree index). The keyed functions are the tweakable hashes $\mathbf{F}(\mathrm{PK.seed}, \mathrm{ADRS}, M_1)$, $\mathbf{H}(\mathrm{PK.seed}, \mathrm{ADRS}, M_2)$ and $\mathbf{T}_\ell(\mathrm{PK.seed}, \mathrm{ADRS}, M_\ell)$ on $n$-byte blocks, the secret-key PRF $\mathrm{PRF}(\mathrm{PK.seed}, \mathrm{SK.seed}, \mathrm{ADRS})$, and the message functions $\mathrm{PRF}_{msg}$ and $H_{msg}$; they are instantiated with SHAKE256 or with SHA-2 using a compressed 22-byte address. The canonical address encoding is injective, and distinct address types have distinct codes.

## Sources

- National Institute of Standards and Technology, "Stateless Hash-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
- Andreas Hülsing and Mikhail Kudinov, "Recovering the Tight Security Proof of SPHINCS+", Cryptology ePrint Archive, Paper 2022/346, 2022.
