# The curvature integral of the central path is bounded in terms of the constraint matrix

This settles [An upper bound for the curvature integral depending only on the constraint matrix](curvature-integral-bounded-by-a.md) in the affirmative: its statement holds.

By Monteiro–Tsuchiya's Theorem 2.4, $F(\infty, 0)$ is bounded by $C n^{3.5} \log(\bar\chi^*_A + n)$ for an
absolute constant $C$, a quantity depending only on $A$.

## Sources

- Oberwolfach Report 2/2005, Optimization and Applications (Oberwolfach, 2005), DOI 10.4171/OWR/2005/02, pp. 121-124 (T. Tsuchiya, joint with R. D. C. Monteiro); resolution: R. D. C. Monteiro and T. Tsuchiya, A strong bound on the integral of the central path curvature and its relationship with the iteration-complexity of primal-dual path-following LP algorithms, Math. Program. 115 (2008), 105-149, DOI 10.1007/s10107-007-0141-5 (preprint Optimization Online 2005/09/1221), §2.1: assumptions A.1 (strictly feasible primal and dual) and A.2 (rows of A linearly independent), curvature κ(ν) = ‖ν ẋ(ν) ṡ(ν)‖^\{1/2\} (7) with the Euclidean norm, I(ν_f, ν_i) = ∫ κ(ν)/ν dν (10), Prop. 2.3(b) (χ̄_A = max ‖G⁻¹A‖ over m × m nonsingular submatrices); Theorem 2.4: I(0, ∞) ≤ O(n^\{3.5\} log(χ̄*_A + n)) with χ̄*_A = inf \{χ̄_\{AD\} : D positive diagonal\}; Lemma 2.1(ii): if κ vanishes somewhere it vanishes everywhere (the case excluded by A.3, where the integral is 0), https://optimization-online.org/wp-content/uploads/2005/09/1221.pdf.
