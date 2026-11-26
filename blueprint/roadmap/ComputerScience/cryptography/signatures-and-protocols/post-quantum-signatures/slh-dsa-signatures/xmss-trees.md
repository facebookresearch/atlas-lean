# XMSS trees and authentication paths in SLH-DSA

An XMSS tree of height $h'$ has as leaves the $2^{h'}$ WOTS+ public keys of one layer and tree address, and each internal node at height $j$ and index $i$ is $\mathbf{H}$ applied, under the tree address with height $j$ and index $i$, to its two children. An XMSS signature on an $n$-byte value for leaf $idx$ is a WOTS+ signature together with the authentication path: the $h'$ sibling nodes on the path to the root. *Public-key reconstruction* (xmss_pkFromSig) recomputes the leaf from the WOTS+ signature and then, for $j = 0, \dots, h' - 1$, combines the current node with the $j$-th sibling, putting the current node first exactly when $\lfloor idx/2^j \rfloor$ is even. The SLH-DSA *hypertree* stacks $d$ layers of XMSS trees of height $h' = h/d$, each tree signing the root of the tree below, and a FORS few-time signature at the bottom signs the message digest.

## Depends on

- [WOTS+ one-time signatures](wots-plus.md)
- [Merkle root](../../../hash-functions/merkle-trees/root.md)

## Sources

- National Institute of Standards and Technology, "Stateless Hash-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
- Andreas Hülsing and Mikhail Kudinov, "Recovering the Tight Security Proof of SPHINCS+", Cryptology ePrint Archive, Paper 2022/346, 2022.
