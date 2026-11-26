# Hecke T

The Hecke sum `heckeT k p f = heckeU k p f + f ∣[k] heckeDiagMatrix p` in weight `k`, for a
function `f` on the upper half-plane. With Mathlib's slash action this is
`heckeT k p f τ = p⁻¹ ∑_{j < p} f ((τ + j) / p) + p ^ (k - 1) f (p τ)` for `p ≠ 0`
(`heckeT_apply`), and `heckeT k 0 f = f`. For `p ≠ 0` it acts on the `q`-expansion coefficients
of a modular form for a group with `1` as a strict period by `coeffHeckeT`
(`ModularFormClass.qCoeff_heckeT`).

On modular forms for `Γ₀(N)` it is the classical Hecke operator `T_p` only for a prime `p` not
dividing `N` (`ModularForm.heckeTLin`); for composite `p` it is not `T_p`, and for a prime
`p ∣ N` the classical operator is `U_p`, given by `heckeU k p` (`ModularForm.heckeULin`). On
forms for a group `GammaH N H` between `Γ₁(N)` and `Γ₀(N)`, the classical `T_p` for a prime
`p ∤ N` is `heckeU k p f + (⟨p⟩ f) ∣[k] heckeDiagMatrix p`, where the diamond operator `⟨p⟩`
slashes by a matrix of `Γ₀(N)` whose lower-right entry is `p` modulo `N`. So the classical
`T_p f` equals `heckeT k p f` exactly when `⟨p⟩ f = f`, for instance when `p` modulo `N` lies in
`H`. In Lean, `CuspForm.coe_heckeTLinH_apply` gives this formula for `CuspForm.heckeTLinH` on
cusp forms for `GammaH N H`, under the explicit hypothesis `CuspForm.StableT N H k p`; when that
hypothesis does not hold, `CuspForm.heckeTLinH` is defined to be zero.
