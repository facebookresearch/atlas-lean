# Sublinear functional encryption from partially hiding FE and structured-seed PRGs

Let $\gamma,\epsilon$ and $d$ be constants and $p$ an efficiently samplable $\lambda$-bit prime. Assume the (subexponential) hardness of SXDH in bilinear groups of order $p$ (which gives a partially hiding FE for functions of degree $2$ in the private input, with ciphertext linear in the private input); LWE with modulus-to-noise ratio $2^{k^{\epsilon}}$, where $k$ is the dimension of the secret (to hide the residual leakage by noise flooding and to build the outer encryption); the existence of a Boolean PRG in $\mathsf{NC}^0$ with polynomial stretch and multilinear degree $d$; and a (subexponentially) $\gamma$-pseudorandom structured-seed PRG over $\mathbb{Z}_p$ with polynomial stretch whose output is degree $2$ in the private seed and computed from the public seed in $\mathsf{arith}\text{-}\mathsf{NC}^0$, with $\gamma$ small enough that $2\gamma+O(1/\lambda)<1$. Then there is a single-key, weakly selective, (subexponentially) indistinguishability-secure public-key FE for polynomial-size circuits that is weakly compact: its encryption time is $\mathrm{poly}(\lambda,l)\cdot S^{1-\sigma}$ for inputs of length $l$, circuits of size $S$ and a constant $\sigma\in(0,1)$. The proof first turns the structured-seed PRG into a perturbation-resilient generator (Theorem 5.1), then builds a single-key, weakly selective secret-key FE for $\mathsf{NC}^0$ (Theorem 5.2), and finally lifts it to all polynomial-size circuits, amplifies security and converts it to public-key FE (Theorem 5.3).

## Proof sketch

Encrypt $x$ with a lattice-based encryption whose decryption, combined with a randomized encoding of the circuit, is computable in low degree from the PRG output; the PRG expands a short seed (encrypted in the partially hiding FE) into the many pseudorandom values needed, so the ciphertext is sublinear in the circuit size. LWE noise floods the small decryption error leaked by the degree-2 computation.

## Depends on

- [The symmetric external Diffie–Hellman assumption](../obfuscation-from-well-founded-assumptions/sxdh-assumption.md)
- [Structured-seed pseudorandom generators](../obfuscation-from-well-founded-assumptions/structured-seed-prg.md)
- [Pseudorandom generators in NC0 with polynomial stretch](../obfuscation-from-well-founded-assumptions/local-prg.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Single-key weakly compact public-key functional encryption](weakly-compact-fe.md)

## Proof depends on

- [Degree-3 decomposable randomized encodings of log-depth computations](nc0-randomized-encoding.md)
- [Partially hiding FE for degree-two private computations from SXDH](phfe-from-sxdh.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317, Theorems 5.1, 5.2 and 5.3.
