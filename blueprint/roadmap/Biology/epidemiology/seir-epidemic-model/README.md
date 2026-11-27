# SEIR epidemic model

- [Solution of the closed SEIR system for times t ≥ 0](is-solution.md)
- [S + E + I + R is constant along a solution for t ≥ 0](total-eq.md)
- [Derivative of the infected total E + I along a solution](has-deriv-at-exposed-add-infected.md)
- [With I(0) > 0, (E + I)'(0) > 0 exactly when R₀ S(0) / N > 1](deriv-exposed-add-infected-pos-iff.md)
- [With σ > 0 and I(0) = 0 < E(0), I'(0) = σ E(0) > 0](deriv-infected-pos-of-exposed.md)
- [For γ ≠ 0, S(t) exp(β R(t) / (γ N)) is constant for t ≥ 0](susceptible-mul-exp-eq.md)

## The equations on an interval

- [Susceptibles in integrating-factor form on an interval](susceptible-eq-mul-exp-of-has-deriv-at.md)
- [Conservation of S + E + I + R on an interval](total-eq-of-has-deriv-at.md)
- [For β, σ, γ, N ≥ 0, the compartments stay nonnegative on an interval](nonneg-of-has-deriv-at.md)

## Formulas and positivity along a solution

- [Susceptibles in integrating-factor form](susceptible-eq-mul-exp.md)
- [Susceptibles stay positive exactly when they start positive](susceptible-pos-iff.md)
- [Susceptibles vanish exactly when they start at zero](susceptible-eq-zero-iff.md)
- [Forward invariance of the nonnegative orthant for β, σ, γ, N ≥ 0](nonneg.md)
- [With nonnegative parameters and data, E(t) ≥ E(0) exp(−σ t) for t ≥ 0](exposed-ge.md)
- [With nonnegative parameters and data, I(t) ≥ I(0) exp(−γ t) for t ≥ 0](infected-ge.md)
- [With σ > 0 and E(0) > 0, infectives are positive at every time t > 0](infected-pos-of-exposed-pos.md)
- [With β, N, S(0), I(0) > 0, E(t) > 0 at every time t > 0](exposed-pos-of-infected-pos.md)

## The SEIR vector field

- [The SEIR vector field on ℝ⁴](seir-field.md)

## Forward-global existence and uniqueness

- [Forward-global nonnegative SEIR solutions for β, σ, γ, N ≥ 0](exists-is-solution-nonneg.md)
- [Forward uniqueness of SEIR solutions](eq-of-initial.md)
- [Forward-global SEIR solutions on the simplex of total N](exists-is-solution-simplex.md)

## Long-time behaviour and final size

- [Final-size relation when S and R have limits](final-size.md)
- [Limits and final size for nonnegative data with σ, γ > 0](tendsto-final-size.md)
- [With E(0) + I(0) > 0, every final-size root x ≤ S(0) equals S∞](final-size-eq-of-root.md)

## The next-generation matrix at the disease-free equilibrium

- [New-infection rates of the SEIR infected compartments](new-infections.md)
- [Transfer rates of the SEIR infected compartments](transfers.md)
- [The SEIR infected rates split as new infections minus transfers](seir-field-infected-eq.md)
- [Jacobian of the new-infection rates at the disease-free equilibrium](has-fderiv-at-new-infections.md)
- [Jacobian of the transfer rates at the disease-free equilibrium](has-fderiv-at-transfers.md)
- [Infected-block Jacobian F − V at the disease-free equilibrium](has-fderiv-at-infected-field.md)
- [For β ≥ 0, the new-infection matrix F is entrywise nonnegative](ngm-f-nonneg.md)
- [For σ, γ > 0, the transfer matrix V is a nonsingular M-matrix](ngm-v-is-nonsingular-mmatrix.md)
- [For β ≥ 0 and σ, γ > 0, the SEIR R₀ = ρ(F V⁻¹) equals β / γ](r0-eq.md)
- [For β ≥ 0, σ, γ > 0 and N ≠ 0, SEIR rate derivatives give R₀ = β / γ](r0-fderiv-eq.md)
- [For σ, γ > 0 and β ≥ 0, F − V is Hurwitz exactly when β < γ](is-hurwitz-iff.md)
- [For σ, γ > 0 and β ≥ 0, F − V has an eigenvalue with Re > 0 iff β > γ](exists-re-pos-iff.md)
- [Herd immunity threshold under gamma-distributed susceptibility or connectivity](heterogeneous-susceptibility-herd-immunity-threshold.md)
