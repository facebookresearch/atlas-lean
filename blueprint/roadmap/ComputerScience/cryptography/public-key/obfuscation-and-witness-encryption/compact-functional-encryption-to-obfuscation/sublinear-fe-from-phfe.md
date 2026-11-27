# Sublinear functional encryption from partially hiding FE and structured-seed PRGs

Assume a partially hiding FE for functions of degree $2$ in the private input (with ciphertext linear in the private input), a structured-seed PRG with stretch $n^{1+\tau}$ whose output is degree $2$ in the private seed and constant-degree in the public seed, and LWE (to hide the residual leakage by noise flooding and to build the outer encryption). Then there is a single-key, selectively secure, weakly compact public-key FE for polynomial-size circuits (with security loss polynomial in the reductions' advantages).

## Proof sketch

Encrypt $x$ with a lattice-based encryption whose decryption, combined with a randomized encoding of the circuit, is computable in low degree from the PRG output; the PRG expands a short seed (encrypted in the partially hiding FE) into the many pseudorandom values needed, so the ciphertext is sublinear in the circuit size. LWE noise floods the small decryption error leaked by the degree-2 computation.

## Depends on

- [Partially hiding functional encryption for degree-two private computations](partially-hiding-fe.md)
- [Structured-seed pseudorandom generators](../obfuscation-from-well-founded-assumptions/structured-seed-prg.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Single-key weakly compact public-key functional encryption](weakly-compact-fe.md)

## Proof depends on

- [Degree-3 decomposable randomized encodings of log-depth computations](nc0-randomized-encoding.md)
- [Partially hiding FE for degree-two private computations from SXDH](phfe-from-sxdh.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317.
