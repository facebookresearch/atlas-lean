---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CDIS.integral_mul_eq_integral_ratio, CDIS.not_forall_integral_withDensity_ratio_eq, CDIS.tendsto_importanceSampling, CDIS.tendsto_importanceSampling_normalized
---

# Importance sampling

CDIS id 99. `E_f[h(X)] = ∫ h (f/g) g` when `g > 0` almost everywhere where `h f ≠ 0` (the
 course says there is no restriction on `g`; a counterexample, as an expectation under `g`, is
 formalized). The plain and self-normalised estimators converge almost surely by the strong law
 of large numbers.

## Depends on

No prerequisite in this chapter.

## Sources

- [Probabilités V, Echantillonnage d'importance](../../sources/cdis-probabilites-v.md)
