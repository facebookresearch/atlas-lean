# HyperNova multi-folding scheme for CCS

There is a public-coin multi-folding scheme that folds an LCCCS instance and a CCCS instance (more generally $\mu$ LCCCS and $\nu$ CCCS instances) into a single LCCCS instance: the parties run the sum-check protocol on $g(X)$, ending at a random point $r'_x$; the prover sends $\sigma_j=\sum_y\widetilde{M}_j(r'_x,y)\widetilde{z}_1(y)$ and $\theta_j=\sum_y\widetilde{M}_j(r'_x,y)\widetilde{z}_2(y)$; the verifier checks the final sum-check claim from these values and, for a random $\rho$, outputs the LCCCS instance $(C_1+\rho C_2,\;u+\rho\cdot 1,\;x_1+\rho x_2,\;r'_x,\;\sigma_j+\rho\theta_j)$. If the commitment is additively homomorphic and binding, the scheme is complete and knowledge sound; the prover's cryptographic cost is a single multi-scalar multiplication of size equal to the number of witness variables, and the verifier performs one group scalar multiplication plus $O(d\log m)$ field operations.

## Proof sketch

Completeness: the sum-check claim equals $\sum_j\gamma^{j}v_j$ by the previous lemma, and at the end point the linear claims $\sigma_j,\theta_j$ combine linearly under $\rho$. Knowledge soundness: extract from two transcripts with distinct $\rho$ the witnesses $z_1,z_2$ (binding pins them to the commitments); sum-check soundness and the zero-check lemma then imply the original LCCCS claims hold and the CCCS instance is satisfying, except with probability $O((d+t)\log m/|\mathbb{F}|)$.

## Depends on

- [Sum-check polynomial for folding an LCCCS and a CCCS instance](multifolding-sumcheck.md)
- [Folding scheme for an NP relation](../relaxed-r1cs-folding-schemes/folding-scheme.md)
- [Linearized committed CCS instances](linearized-committed-ccs.md)

## Proof depends on

- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573.
