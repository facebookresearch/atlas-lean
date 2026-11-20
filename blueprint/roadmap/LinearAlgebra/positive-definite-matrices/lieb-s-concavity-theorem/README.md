# Lieb's concavity theorem

Lieb's 1973 paper on the Wigner–Yanase–Dyson conjecture proves two concavity theorems, and both carry his name. Carlen's lecture notes (Theorem 6.1 of the 2009 draft) call Lieb's concavity theorem the joint concavity of $(A, B) \mapsto \operatorname{tr}(K^* A^q K B^r)$ on pairs of positive-definite matrices, for $q, r \ge 0$ with $q + r \le 1$. Tropp's monograph (Theorem 3.4.1) gives the name to the concavity of $A \mapsto \operatorname{tr}\exp(H + \log A)$ on the positive-definite cone, for every fixed Hermitian $H$, proved in the same paper. That exponential form belongs to the family of trace inequalities with those of Peierls, Klein and von Neumann, and in probability it is the engine of matrix concentration: with Jensen's inequality it makes matrix cumulant generating functions subadditive.

Strong subadditivity of von Neumann entropy, $S(\rho_{123}) + S(\rho_2) \le S(\rho_{12}) + S(\rho_{23})$, follows from the joint form: it gives the joint convexity of quantum relative entropy and its monotonicity under partial traces (Carlen, Theorems 6.3, 6.4 and 6.6; Lieb and Ruskai, 1973).

- [Lieb's concavity theorem, joint form](lieb-concavity-trace-rpow.md)
- [Lieb's concavity theorem, case `r = 0`](lieb-concavity-trace-rpow-of-right-eq-ze.md)
- [Lieb's concavity theorem, case `q = 0`](lieb-concavity-trace-rpow-of-left-eq-zer.md)
- [Concavity of `A ↦ tr (K* A^q K)`](concave-on-re-trace-conj-rpow.md)
- [Lieb's concavity theorem](lieb-concavity.md)

## Related topics

- [Matrix concentration inequalities](../../../Probability/concentration-inequalities/matrix-concentration-inequalities/README.md)
- [Peierls and Klein inequalities](../../../Analysis/operator-theory/eigenvalue-inequalities/peierls-and-klein-inequalities/README.md)
- [Von Neumann's trace inequality](../von-neumann-s-trace-inequality/README.md)
