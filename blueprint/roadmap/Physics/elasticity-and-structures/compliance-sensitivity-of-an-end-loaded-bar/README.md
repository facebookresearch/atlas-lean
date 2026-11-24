# Compliance sensitivity of an end-loaded bar

A bar of length $L > 0$ and axial rigidity $EA \ne 0$ (a force; $EA > 0$ in the physical reading),
fixed at $x = 0$ and loaded at $x = L$ by an end force $F$ along $+x$ with no distributed load, has
the displacement $u(x) = F x / EA$ on $[0, L]$. As a spring it has the stiffness $k = EA / L$ and
the tip displacement $u(L) = F / k$, and the compliance $J(F, k) = F \cdot F / k = F^2 / k$ is the
work of the end force. For $k > 0$ its derivative is $dJ / dk = -F^2 / k^2$, negative for $F \ne 0$.
The stiffness is then a design variable in an interval $[k_{\min}, k_{\max}]$ with $k_{\min} > 0$.
For forces of magnitude at most $F_{\max}$ and stiffnesses at least $k_{\min}$ the change of $J$ is
at most $(2 F_{\max} / k_{\min})\, |F - \hat F| + (F_{\max}^2 / k_{\min}^2)\, |k - \hat k|$, and for
$k \ge k_{\min}$ a residual of the equilibrium $k\, u_{\mathrm{tip}} = F$ bounds the state and
compliance errors through the factor $1 / k_{\min}$, while over all $k > 0$ no constant turns it
into a bound on the state error, nor, for $F \ne 0$, on the compliance error. The quotients $F / k$
and $EA / L$ are $0$ at $k = 0$ and $L = 0$ by the convention $x / 0 = 0$.

## The bar under an end force with no distributed load

- [With no distributed load the constructed bar displacement is F x / EA](fixed-traction-displacement-zero-load.md)
- [The linear displacement F x / EA solves the end-loaded bar problem](is-fixed-traction-solution-zero-load.md)
- [Every solution of the end-loaded bar problem is F x / EA on the bar](eq-on-zero-load-of-is-fixed-traction-sol.md)

## Spring stiffness, tip displacement, compliance and the adjoint

- [Effective axial stiffness EA / L of a bar](axial-stiffness.md)
- [Tip displacement F / k of a spring under an end force](tip-displacement.md)
- [Compliance: the work of the end force on the tip displacement](compliance.md)
- [Scalar adjoint F / k of the compliance](adjoint-displacement.md)
- [Positive rigidity and length give a positive axial stiffness](axial-stiffness-pos.md)
- [The tip displacement of the end-loaded bar is F / k with k = EA / L](tip-eq-of-is-fixed-traction-solution.md)
- [The scalar adjoint solves k p = F for a nonzero stiffness](stiffness-mul-adjoint-displacement.md)

## Sensitivity of the compliance

- [For k > 0 the compliance derivative is −p times the tip displacement](has-deriv-at-compliance.md)
- [Minus adjoint times tip displacement is −F²/k², for every k](neg-adjoint-displacement-mul-tip-displac.md)
- [Compliance derivative −F²/k² within a positive feasible interval](has-deriv-within-at-compliance-icc.md)

## Feasible directions

- [Feasible directions at a design in a stiffness interval](feasible-directions.md)
- [If kmin < kmax, the feasible directions at kmin are the d ≥ 0](feasible-directions-left.md)
- [If kmin < kmax, the feasible directions at kmax are the d ≤ 0](feasible-directions-right.md)
- [At an interior design every direction is feasible](feasible-directions-interior.md)
- [On a degenerate interval only the zero direction is feasible](feasible-directions-self.md)

## Endpoints: one-sided conditions, not stationarity

- [For a nonzero force the compliance has no stationary point at k > 0](deriv-compliance-ne-zero.md)
- [For F ≠ 0 the upper endpoint meets a one-sided first-order condition](compliance-upper-endpoint.md)

## Units

- [A force per length has the translational stiffness dimension M T⁻²](axial-stiffness-dimension.md)
- [A force over a translational stiffness has the length dimension](tip-displacement-dimension.md)
- [A force times a length has the energy dimension](compliance-dimension.md)
- [An energy per translational stiffness has dimension length squared](compliance-sensitivity-dimension.md)

## Compliance error: one-parameter steps

- [The compliance equals F² / k, including k = 0 where both vanish](compliance-eq-sq-div.md)
- [Force step: bound for force magnitudes at most Fmax and k ≥ kmin > 0](abs-compliance-sub-force-le.md)
- [Stiffness step: compliance bound for stiffnesses at least kmin > 0](abs-compliance-sub-stiffness-le.md)

## Compliance error: composition

- [Compliance error between two admissible parameter points](abs-compliance-sub-compliance-le.md)
- [Compliance error bound: parameter steps plus four supplied error terms](abs-compliance-sub-computed-le.md)

## Residuals and the stability constant

- [For k ≥ kmin > 0 the residual bounds state and compliance errors](abs-sub-le-residual-div.md)
- [No residual bound on the state error uniform in k > 0](not-exists-residual-state-error-bound.md)
- [For F ≠ 0, no residual bound on the compliance error uniform in k > 0](not-exists-residual-compliance-error-bou.md)
- [For F ≠ 0, neither error has a residual bound uniform in k > 0](not-exists-residual-error-bound.md)
