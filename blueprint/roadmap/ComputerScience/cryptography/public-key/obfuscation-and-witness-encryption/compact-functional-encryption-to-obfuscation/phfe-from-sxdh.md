# Partially hiding FE for degree-two private computations from SXDH

Assuming the SXDH assumption in asymmetric bilinear groups of prime order $p$, for every polynomial bound $B = B(\lambda)$ there is a secret-key partially hiding functional encryption scheme for the full class $(\mathsf{arith}\text{-}\mathsf{NC}^{1},\deg 2)$ over $\mathbb{Z}_p$ (arithmetic $\mathsf{NC}^{1}$ computation on the public input, degree at most $2$ in the private input) that satisfies $B$-bounded correctness, is simulation secure against collusions (weakly selective, any polynomial number of keys and ciphertexts), and has linear efficiency: ciphertexts of size $\mathrm{poly}(\lambda)\cdot(|\mathbf{x}|+|\mathbf{y}|)$. For every function $f$ in the class and every input $(\mathbf{x},\mathbf{y})$, pairings yield $g_T^{f(\mathbf{x},\mathbf{y})}$ in the target group, and $\mathsf{Dec}$ recovers $f(\mathbf{x},\mathbf{y})$ in time $\mathrm{poly}(\lambda, B)$ by brute-force discrete logarithm whenever the evaluation satisfies $f(\mathbf{x},\mathbf{y}) \in \{-B, \dots, B\}$. Jain, Lin and Sahai use this scheme in their construction of iO from well-founded assumptions and credit its construction to their earlier work.

## Proof sketch

The private input is encoded in the two source groups with function-hiding inner-product functional encryption, so that pairing the encodings computes the degree-2 monomials under random masks that the key removes, while the computation on the public input, which is in the clear, is carried out on the key side. Security reduces to SXDH by hybrid arguments on the masks.

## Depends on

- [Partially hiding functional encryption for degree-two private computations](partially-hiding-fe.md)
- [The symmetric external Diffie–Hellman assumption](../obfuscation-from-well-founded-assumptions/sxdh-assumption.md)
- [Bilinear groups](../../advanced-encryption-and-pairings/bilinear-groups.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317, Appendix B (ingredients of the construction; the decryption step of the $\mathsf{NC}^0$-FE construction, which extracts each output from $g_T$ by brute-force discrete logarithm because it has $\operatorname{poly}(\lambda)$ magnitude).
- Aayush Jain, Huijia Lin, Amit Sahai, "Simplifying Constructions and Assumptions for iO", IACR ePrint 2019/1252 (2019), Theorem 3 and Section 6 (the SXDH construction; its bilinear inner-product scheme decrypts in two steps, the second computing a discrete logarithm when the value lies in $[-B, B]$, under $B$-correctness).
