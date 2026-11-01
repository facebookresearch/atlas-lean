---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Algebra.PermutationPolynomialsWanted.finiteField_sum_eval_mul_pow_eq_id_iff
---

# Finite Field sum eval mul pow eq id iff

Ding and Zieve's Theorem 2: for `q = p ^ ℓ > 2` and
`k % (p * (q - 1)) = 1`, the polynomial action
`c ↦ ∑ n ∈ [1,k], h.eval n * c ^ n` is the identity on a finite
field of cardinality `q` if and only if `h.eval 1 = 1` and either
`k % p ^ 2 = 1` or
`∑ j ∈ [1, h.natDegree / (p - 1)], h.coeff (j * (p - 1)) = 0`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Algebra.PermutationPolynomialsWanted](../../../../sources/v2/WantedExt.md)
- Zhiguo Ding and Michael E. Zieve, "Permutation Polynomials of the Form `∑_{n=1}^k h(n) X^n`", Theorem 2.
