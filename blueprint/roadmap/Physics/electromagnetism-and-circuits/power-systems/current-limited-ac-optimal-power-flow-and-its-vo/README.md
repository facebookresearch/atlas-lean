# Current-limited AC optimal power flow and its voltage lift

## Network matrices and the optimal power flow problem

- [Bus admittance matrix of a network](bus-admittance.md)
- [Voltage lift of a complex voltage vector](voltage-lift.md)
- [Lifted complex injection at a bus](lifted-injection.md)
- [Real trace pairing of complex matrices](pairing.md)
- [Matrix keeping one row of a square matrix](row-select.md)
- [Coefficient matrix of the active power at a bus](active-coeff.md)
- [Coefficient matrix of the reactive power at a bus](reactive-coeff.md)
- [Coefficient matrix of the squared voltage magnitude at a bus](voltage-coeff.md)
- [Coefficient matrix of the squared current on a branch](branch-current-coeff.md)
- [Data of a current-limited AC optimal power flow problem](current-limited-opf.md)
- [Bus admittance matrix of an optimal power flow instance](admittance.md)
- [AC feasibility of a voltage vector](ac-feasible.md)
- [Linear active-generation cost of a voltage vector](ac-cost.md)
- [Feasibility for the semidefinite relaxation](sdp-feasible.md)
- [Linear active-generation cost of a matrix in the relaxation](sdp-cost.md)

## The voltage lift

- [Entries of the voltage lift](voltage-lift-apply.md)
- [The voltage lift is positive semidefinite](voltage-lift-pos-semidef.md)
- [The voltage lift is Hermitian](voltage-lift-is-hermitian.md)
- [The voltage lift has rank at most one](voltage-lift-rank-le-one.md)
- [The zero voltage vector lifts to the zero matrix](voltage-lift-zero.md)
- [The voltage lift is unchanged by a common unit-modulus factor](voltage-lift-unit-mul.md)

## Injections through the bus admittance matrix

- [The bus admittance matrix maps voltages to nodal current injections](bus-admittance-mul-vec-eq-node-injection.md)
- [Bus complex power as a linear function of the voltage lift](node-complex-power-eq-lifted-injection.md)

## Hermitian coefficient matrices and real affine constraints

- [The pairing with a fixed matrix is real-linear](is-linear-map-pairing.md)
- [The active-power coefficient matrix is Hermitian](active-coeff-is-hermitian.md)
- [The reactive-power coefficient matrix is Hermitian](reactive-coeff-is-hermitian.md)
- [The voltage coefficient matrix is Hermitian](voltage-coeff-is-hermitian.md)
- [The branch-current coefficient matrix is Hermitian](branch-current-coeff-is-hermitian.md)
- [Real part of the lifted injection as a pairing, for Hermitian W](re-lifted-injection-eq-pairing.md)
- [Imaginary part of the lifted injection as a pairing, for Hermitian W](im-lifted-injection-eq-pairing.md)
- [The voltage pairing reads the real part of a diagonal entry](pairing-voltage-coeff.md)

## Exactness on lifts

- [On a lift, the active pairing equals the active power at the bus](pairing-active-coeff-voltage-lift.md)
- [On a lift, the reactive pairing equals the reactive power at the bus](pairing-reactive-coeff-voltage-lift.md)
- [On a lift, the voltage pairing is the squared voltage magnitude](pairing-voltage-coeff-voltage-lift.md)
- [On a lift, the branch-current pairing is the squared branch current](pairing-branch-current-coeff-voltage-lif.md)

## Feasibility, cost and the sound relaxation

- [A voltage vector is AC feasible exactly when its lift is SDP feasible](ac-feasible-iff-sdp-feasible-voltage-lif.md)
- [The relaxation cost of a lift equals the AC cost](sdp-cost-voltage-lift.md)
- [Soundness of the semidefinite relaxation](current-limited-aclift-sound.md)
- [Combined properties of the voltage lift and the relaxation](current-limited-aclift-spec.md)

## Two-bus validation

- [Two-bus test instance with one unit-conductance branch](two-bus-example.md)
- [Two-bus example: a feasible voltage whose lift has the same cost 1/4](two-bus-rank-one-witness.md)
- [Two-bus example: the identity is relaxation-feasible but not a lift](two-bus-rank-two-relaxed-not-lift.md)
