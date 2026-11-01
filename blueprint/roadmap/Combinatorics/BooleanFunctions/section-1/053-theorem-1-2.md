---
article_id: af_c076a56c257d3f39d78aba23
declaration: theorem
origin: cited
statement: formalized
lean: BooleanFourier.majority_is_stablest
---

# Theorem 1.2 (Section 1, Noise stability and noise sensitivity)

For all $\rho > 0$, $\delta > 0$ there is $\tau > 0$ such that if $f \colon \{-1,1\}^n \to \{-1,1\}$ is balanced, and $I_i[f] \leqslant \tau$ for all $i \in [n]$, then $\operatorname{Stab}_{\rho}(f) \leqslant \operatorname{Stab}_{\rho}(\operatorname{Majority}) + \delta$.

## Depends on

- [Definition 1.1 (Noise Stability)](052-noise-stability.md)
- [Definition 2.2 (Lecture 4, Section 2)](../lecture-4/007-definition-2-2.md)

## Proof depends on

- [Claim 2.4 (Lecture 5, Section 2.2)](../lecture-5/032-claim-2-4.md)

## Sources

- [MIT 18.218 Analysis of Boolean Functions (Spring 2021), Section 1, Noise stability and noise sensitivity](../../../../sources/v1/BooleanFunctions.md)
