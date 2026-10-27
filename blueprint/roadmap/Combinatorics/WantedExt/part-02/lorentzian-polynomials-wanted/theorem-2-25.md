---
article_id: af_14162ef85fad6dadb099869d
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.LorentzianPolynomialsWanted.LorentzianPolynomials.theorem_2_25
---

# Theorem 2 25

Statement of Theorem 2.25:

The closure of `Ŀ n d` in `H n d` is `L n d`.

The paper allows `n` and `d` to be nonnegative, but the theorem is false for `n = 0` and `d = 2`
where `Ŀ 0 2 = {f ∈ P 0 2 | ℋ_f is nonsingular and has exactly one positive eigenvalue } = ∅`
since the `0×0` Hessian matrix of `f` cannot have a positive eigenvalue, but `L 0 2 = S 0 2`
contains the zero polynomial since the zero polynomial is homogeneous of degree `2`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.LorentzianPolynomialsWanted](../../../../../sources/v2/WantedExt.md)
- P. Brändén and J. Huh, `Lorentzian polynomials`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-LorentzianPolynomials.lean Via leanprover/lean-eval@38361be, problem `annals_lorentzian_polynomials`.
