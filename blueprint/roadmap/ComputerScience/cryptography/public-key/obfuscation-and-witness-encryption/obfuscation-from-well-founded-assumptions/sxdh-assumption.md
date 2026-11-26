# The symmetric external Diffie–Hellman assumption

Let $(\mathbb{G}_1,\mathbb{G}_2,\mathbb{G}_T,e,g_1,g_2,p)$ be an asymmetric bilinear group of prime order $p$ with no efficiently computable homomorphism between $\mathbb{G}_1$ and $\mathbb{G}_2$. The *SXDH assumption* states that the decisional Diffie–Hellman problem is hard in both source groups: for $b\in\{1,2\}$ and uniform $x,y,z\in\mathbb{Z}_p$, the tuples $(g_b,g_b^{x},g_b^{y},g_b^{xy})$ and $(g_b,g_b^{x},g_b^{y},g_b^{z})$ are computationally indistinguishable given the group description.

## Depends on

- [Bilinear groups](../../advanced-encryption-and-pairings/bilinear-groups.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317.
