# A bounded orthonormal sequence of infinite codimension with no same-bound completion

There is a real orthonormal sequence on the unit interval bounded pointwise by $2$ whose
closed span in $L^2$ has infinite-dimensional orthogonal complement. No complete orthonormal
sequence bounded by $2$ contains it.

Rescale the sine basis to $[0,4/5]$. Indicators of disjoint positive-length subintervals
of $(4/5,1]$ give infinitely many independent vectors in the complement. Every member of the
complement bounded by $2$ has squared norm at most $4/5$.

## Sources

- K. S. Kazarian, “On a problem of S. Banach from The Scottish book”, Proc. Amer. Math. Soc. 110 (1990), 881–887. The abstract gives an infinite-codimension example whose complement contains no nonzero bounded function. The interval construction above uses the real sine basis from `MathlibExt.Analysis.ODE.GreensOperator`.
