# Robust linear programming

In robust optimization (Ben-Tal and Nemirovski) the data of a linear program are only known to lie in an uncertainty set, and a *robust feasible* solution must satisfy every constraint for all realizations of the data; the robust counterpart minimizes the worst-case objective over robust feasible solutions. When the data of each constraint run through an ellipsoid, the image of a unit ball under an affine map, the [minimum of a linear form over the unit ball](forall-norm-le-one-le-add-inner-iff.md) turns each uncertain [linear constraint](robust-linear-constraint-iff.md) and the uncertain [objective](robust-objective-le-iff.md) into a conic quadratic constraint, so the robust counterpart is a tractable conic quadratic program. Uncertain linear programs with conic quadratically representable uncertainty sets more generally lead to conic programs.

- [Minimum of a linear form over the unit ball](forall-norm-le-one-le-add-inner-iff.md)
- [Robust counterpart of a linear constraint under ellipsoidal uncertainty](robust-linear-constraint-iff.md)
- [Robust counterpart of a linear objective under ellipsoidal uncertainty](robust-objective-le-iff.md)
- [Robust counterparts for finite, box and polyhedral uncertainty](finite-box-and-polyhedral-robust-counterparts.md)
- [Duality for distributional robustness over a finite transport ball](finite-support-wasserstein-robustness.md)

## Related topics

- [Linear programming](../linear-programming/README.md): the nominal problems whose data the uncertainty sets perturb.
