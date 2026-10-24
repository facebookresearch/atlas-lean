---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.subsequence_secondOrderRecurrence
---

# Velez Uniform Distribution Wanted

Subsequences of a second-order linear recurrence are again
second-order: if `w (n + 2) = P * w (n + 1) - Q * w n` for all `n`,
then for positive `t` and any shift `r` the subsequence
`n ↦ w (t * n + r)` satisfies the recurrence with coefficients
`V_t` and `Q ^ t`, and the discriminants are related by
`V_t ^ 2 - 4 * Q ^ t = U_t ^ 2 * (P ^ 2 - 4 * Q)`, where `U` and `V`
are the Lucas sequences `lucasU` and `lucasV` for the parameters.

The paper writes the recurrence as `w_{n+2} = a w_{n+1} + b w_n`
with subsequence coefficients `a' = v_t(a, b)` and
`b' = (-1) ^ (t + 1) * b ^ t` and discriminant
`D(a, b) = a ^ 2 + 4 * b`; this is the same statement in the
repository convention `P = a`, `Q = -b` (so `b' = -Q ^ t` in the
`signed` position). The paper's sentence identifying the new
characteristic roots as `α ^ t` and `β ^ t` is not formalized.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.VelezUniformDistributionWanted](../../../../sources/v2/WantedExt.md)
- Somer and Křížek, *Generalization of a Theorem of Vélez on Uniform Distribution in Second-Order Linear Recurrences*, INTEGERS 25 (2025), Article A1, Theorem 2.4 (`integers-2025-A1-thm-2-4`).
