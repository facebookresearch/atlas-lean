# Soundness of BCS-compiled FRI in the random oracle model

Compile (batched, smooth or binary) FRI with the BCS transform using digest length $\sigma$. For every prover making at most $t_{FS}$ Fiat–Shamir and $t_{MT}$ Merkle queries, the probability of producing an accepted proof for a word that is $e$-far from the Reed–Solomon code is at most

$$
(t_{FS} + k)\cdot \max\Bigl(\max_i \varepsilon_i^{\mathrm{FRI}},\ \Bigl(1 - \frac{e}{2^d}\Bigr)^{q}\Bigr) + O\!\left(\frac{t_{MT}^2}{2^\sigma}\right),
$$

where $k$ is the number of verifier challenges of the compiled FRI protocol (the verifier's own Fiat–Shamir queries), with the FRI round errors $\varepsilon_i^{\mathrm{FRI}}$ from the unique-decoding or Johnson-regime round-by-round analysis, and with separate prover and verifier Merkle budgets permitted.

## Proof sketch

Instantiate the BCS soundness theorem with the round-by-round soundness of FRI.

## Depends on

- [The FRI protocol](fri-protocol.md)
- [The BCS transform](../interactive-oracle-proofs/bcs-transform.md)

## Proof depends on

- [Soundness and straight-line knowledge soundness of the BCS transform](../interactive-oracle-proofs/bcs-soundness.md)
- [Round-by-round soundness of FRI](fri-round-by-round-soundness.md)

## Sources

- Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner, "Interactive Oracle Proofs", Theory of Cryptography – TCC 2016-B, Part II, 2016.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
- Eli Ben-Sasson et al., "Proximity Gaps for Reed–Solomon Codes", Journal of the ACM, 2023.
