# SNARGs for P from sub-exponential DDH and quadratic residuosity

Assuming sub-exponential hardness of the decisional Diffie–Hellman assumption in a group (and, in a second construction, sub-exponential hardness of quadratic residuosity), there exist publicly verifiable SNARGs for all polynomial-time deterministic computations with proof size, reference string size and verification time $\mathrm{poly}(\lambda,\log T)$; in particular SNARGs for P do not require lattice assumptions.

## Proof sketch

Construct correlation-intractable hash families for the relevant bad-challenge relations from the group assumptions (with sub-exponential hardness used to tolerate guessing), obtain somewhere extractable BARGs, and apply the delegation template for deterministic computations.

## Depends on

- [Delegation for deterministic computation from BARGs and somewhere extractable commitments](snarg-from-barg-and-hash.md)
- [Correlation-intractable hash families](correlation-intractability.md)
- [Discrete-logarithm experiment](../../public-key/hardness-assumptions/dlog-game.md)

## Proof depends on

- [Delegation for deterministic computation from BARGs and somewhere extractable commitments](snarg-from-barg-and-hash.md)

## Sources

- James Hulett, Ruta Jawale, Dakshita Khurana, Akshayaram Srinivasan, "SNARGs for P from Sub-exponential DDH and QR", EUROCRYPT (2022).
