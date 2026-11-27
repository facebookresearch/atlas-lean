# BGW secret sharing and protocol correctness

## Share algebra: product degree and recombination

- [Nat Degree mul le two mul](nat-degree-mul-le-two-mul.md)
- [Recombination vector for degree-2t sharings](exists-recombination-vector.md)
- [Too few evaluation points do not determine the secret](exists-ambiguous-sharings.md)
- [No recombination vector with too few points](no-recombination-vector-of-le.md)
- [Shamir authorized coalitions](shamir-authorized-iff.md)
- [Recombination vector over the Shamir evaluation points](shamir-exists-recombination-vector.md)

## Degree-reduction re-sharing: uniformity of the received-subshare matrix

- [Joint subshare matrix over a list of dealers](dealer-views-aux.md)
- [Joint distribution of the re-shared subshares seen by a coalition](dealer-views.md)
- [Rows outside the dealer list keep their base value](dealer-views-aux-map-eq-pure-of-not-mem.md)
- [Marginal of the joint view at a listed dealer](dealer-views-aux-map-mem.md)
- [Joint dealer views depend only on the listed dealers](dealer-views-aux-congr.md)
- [Marginal of the joint subshare matrix at one dealer](dealer-views-map-eval.md)
- [Joint subshare law is determined by the per-dealer views](dealer-views-eq-of-forall-eq.md)
- [Re-shared subshares hide the values from small coalitions](dealer-views-eq-of-unauthorized.md)
- [Re-shared subshares hide the values (agreement form)](dealer-views-eq-of-agree-on.md)
- [The empty coalition learns nothing from one Shamir sharing](view-dist-of-empty-eq.md)
- [The empty coalition sees a value-independent subshare matrix](dealer-views-empty-eq.md)
- [A single dealer reveals nothing to an unauthorized coalition](dealer-views-aux-singleton-eq.md)

## Protocol correctness under honest execution

- [Arith Op](arith-op.md)
- [Arith Signature](arith-signature.md)
- [Arithmetic interpretation of addition and multiplication gates](arith-interp.md)
- [Degree bound gives a natural-degree bound](poly-nat-degree-le-of-degree-lt-succ.md)
- [Natural-degree bound gives a degree bound](poly-degree-lt-succ-of-nat-degree-le.md)
- [Constant coefficient is evaluation at zero](poly-constant-coeff-eq-eval-zero.md)
- [Sharing polynomial of a new BGW gate](new-gate-poly.md)
- [Gate sharing polynomials of a BGW program](gate-polys.md)
- [Input sharing polynomials of a BGW program](input-polys.md)
- [Input polynomials share their inputs](input-polys-ok.md)
- [A new BGW gate polynomial shares the correct value](new-gate-poly-ok.md)
- [BGW gate polynomials share the correct values](gate-polys-ok.md)
- [Every wire polynomial shares its trace value](wire-poly-ok.md)
- [Input shares of a BGW program](input-shares.md)
- [Share-level execution of a new BGW gate](new-gate-share.md)
- [Share-level execution of the gates of a BGW program](gate-shares.md)
- [Share-level execution of a BGW program](exec-share.md)
- [Input shares agree with the input polynomials](input-shares-bridge.md)
- [A new gate share agrees with its gate polynomial](new-gate-share-bridge.md)
- [Gate shares agree with the gate polynomials](gate-shares-bridge.md)
- [Share-level execution agrees with the witness polynomials](exec-share-bridge.md)
- [Output shares of a BGW execution](proto-shares.md)
- [Correctness of honest BGW execution](protocol-correct.md)
- [A single recombination vector makes BGW correct](protocol-correct-exists.md)
