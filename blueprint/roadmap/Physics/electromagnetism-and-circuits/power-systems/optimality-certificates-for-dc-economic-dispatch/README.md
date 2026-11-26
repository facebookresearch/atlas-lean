# Optimality certificates for DC economic dispatch

## Rational data and the rational linear program

- [Real values of a rational vector](cast-vec.md)
- [Rational incidence matrix of a network](rat-incidence.md)
- [Rational weighted Laplacian of a network](rat-laplacian.md)
- [Rational branch-flow coefficient matrix](rat-branch-flow-matrix.md)
- [Rational generator-to-bus incidence matrix](rat-generator-incidence.md)
- [Rational row selecting the reference angle](rat-reference-row.md)
- [Rational constraint rows on the free variables](rat-free-rows.md)
- [Rational constraint matrix on generation and angles](rat-free-constraint-matrix.md)
- [Rational constraint matrix of the dispatch linear program](rat-lp-matrix.md)
- [Rational right-hand side of the dispatch linear program](rat-lp-rhs.md)
- [Rational objective of the dispatch linear program](rat-lp-objective.md)
- [Rational LP point encoding a rational dispatch](rat-encode.md)

## Dual witnesses

- [LP dual vector of a dispatch dual witness](dual-vector.md)
- [Certified lower bound on the dispatch cost](dual-lower-bound.md)
- [Dual feasibility of a dispatch dual witness](is-dual-feasible.md)

## The certificate checker

- [Exact rational certificate checker for DC dispatch](checks-dispatch-certificate.md)

## Rational and real linear programs

- [The rational LP matrix casts to the real LP matrix](rat-lp-matrix-map.md)
- [The rational right-hand side casts to the real one](cast-vec-rat-lp-rhs.md)
- [The rational objective casts to the real objective](cast-vec-rat-lp-objective.md)
- [The rational encoding casts to the real encoding](cast-vec-rat-encode.md)
- [The encoded witness passes the primal test iff it is feasible](rat-primal-feasible-iff.md)
- [The dual vector passes the dual test iff the witness is dual feasible](dual-vector-feasible-iff.md)
- [The dual objective of the dual vector is minus the lower bound](rat-lp-rhs-dot-product-dual-vector.md)
- [The objective at the encoded witness is minus its cost](rat-lp-objective-dot-product-rat-encode.md)

## Acceptance and rejection

- [Accepted witnesses are exactly the feasible ones within the gap budget](checks-dispatch-certificate-eq-true-iff.md)
- [The checker rejects an infeasible primal witness](checks-eq-false-of-not-dispatch-feasible.md)
- [The checker rejects a dual witness that is not dual feasible](checks-eq-false-of-not-dual-feasible.md)
- [The checker rejects a witness whose gap exceeds the budget](checks-eq-false-of-lt-gap.md)

## Soundness through the encoding

- [An accepted certificate solves the real linear program up to ε](checks-lp-certificate.md)

## Optimality from an accepted certificate

- [An accepted certificate gives an ε-optimal dispatch](dispatch-certificate-correct.md)
- [A certificate accepted with zero gap proves optimality](dispatch-optimal-of-checks-zero.md)
