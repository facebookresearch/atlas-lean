# Dual certificates for AC optimal power flow

## The relaxation in factored-certificate form

- [Objective matrix of the AC power flow relaxation](objective-matrix.md)
- [Constant term of the relaxation objective](objective-offset.md)
- [Coefficient matrices of the relaxation constraints](constraint-coeff.md)
- [Right-hand sides of the relaxation constraints](constraint-bound.md)
- [Enumeration of the relaxation constraints](constraint-index.md)
- [Constraint coefficient matrices in enumerated order](lifted-coeff.md)
- [Constraint right-hand sides in enumerated order](lifted-bound.md)

## Dual certificates

- [Dual witness for the AC power flow relaxation](acdual-certificate.md)
- [Sign check of an AC dual witness](nonneg.md)
- [Multipliers of an AC dual witness by constraint](multiplier.md)
- [Multipliers of an AC dual witness in enumerated order](lifted-multiplier.md)
- [Dual slack matrix of an AC dual witness](dual-slack.md)
- [Certified lower bound of an AC dual witness](certified-lower-bound.md)

## Translation into the factored-certificate form

- [The objective matrix is Hermitian](objective-matrix-is-hermitian.md)
- [Every constraint coefficient matrix is Hermitian](lifted-coeff-is-hermitian.md)
- [The relaxation cost in terms of the objective matrix](sdp-cost-eq-objective.md)
- [Relaxation feasibility in enumerated constraint form](sdp-feasible-iff-lifted.md)
- [The sign check gives nonnegative enumerated multipliers](lifted-multiplier-nonneg.md)
- [The dual slack in enumerated constraint form](dual-slack-eq-lifted.md)
- [The certified bound in enumerated constraint form](certified-lower-bound-eq-lifted.md)

## Soundness and optimality

- [A checked AC dual witness bounds the relaxation cost](certified-lower-bound-le-sdp-cost.md)
- [A checked AC dual witness bounds the AC cost](certified-lower-bound-le-ac-cost.md)
- [An AC-feasible voltage attaining the certified bound is optimal](ac-optimal-of-ac-cost-eq-certified-lower.md)
- [Soundness of AC voltage dual certificates](ac-voltage-certificate-correct.md)

## Two-bus validation

- [Two-bus current-limited power flow example](two-bus-cert-example.md)
- [Exact dual witness for the two-bus example](two-bus-certificate.md)
- [The certified optimal voltage of the two-bus example](two-bus-optimal-voltage.md)
- [The two-bus witness passes the checks with bound 3/2](two-bus-certificate-exact.md)
- [The certified voltage is a global minimizer of the two-bus problem](two-bus-global-optimum.md)
- [A relaxed point of the two-bus example](two-bus-relaxed-point.md)
- [The two-bus relaxed point is feasible but not a voltage lift](two-bus-relaxed-point-not-lift.md)
- [A stationary voltage of the two-bus example](two-bus-stationary-voltage.md)
- [Stationarity multipliers at the two-bus stationary voltage](two-bus-stationary-multipliers.md)
- [A stationary point with matching bound is not a certificate](two-bus-stationary-point-not-certificate.md)
