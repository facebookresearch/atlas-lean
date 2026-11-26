# Monteiro–Tsuchiya theorem on the curvature integral of the central path

This settles [Monteiro–Tsuchiya bound on the curvature integral](curvature-integral-big-o.md) in the affirmative: its statement holds.

Monteiro and Tsuchiya prove `F(∞, 0) = I(0, ∞) ≤ O(n^{3.5} log(χ̄*_A + n))`, the
conjectured bound.

## Sources

- Oberwolfach Report 2/2005, Optimization and Applications (Oberwolfach, 2005), DOI 10.4171/OWR/2005/02, pp. 121-124 (T. Tsuchiya, joint with R. D. C. Monteiro); resolution: R. D. C. Monteiro and T. Tsuchiya, A strong bound on the integral of the central path curvature and its relationship with the iteration-complexity of primal-dual path-following LP algorithms, Math. Program. 115 (2008), 105-149, DOI 10.1007/s10107-007-0141-5 (preprint Optimization Online 2005/09/1221), §2.1: assumptions A.1 (strictly feasible primal and dual) and A.2 (rows of A linearly independent), curvature κ(ν) = ‖ν ẋ(ν) ṡ(ν)‖^\{1/2\} (7) with the Euclidean norm, I(ν_f, ν_i) = ∫ κ(ν)/ν dν (10), Prop. 2.3(b) (χ̄_A = max ‖G⁻¹A‖ over m × m nonsingular submatrices); Theorem 2.4: I(0, ∞) ≤ O(n^\{3.5\} log(χ̄*_A + n)) with χ̄*_A = inf \{χ̄_\{AD\} : D positive diagonal\}; Lemma 2.1(ii): if κ vanishes somewhere it vanishes everywhere (the case excluded by A.3, where the integral is 0), https://optimization-online.org/wp-content/uploads/2005/09/1221.pdf.
