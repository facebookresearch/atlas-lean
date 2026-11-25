# f-divergences

For a convex function $f$ with $f(1) = 0$, the f-divergence of a distribution $P$ from $Q$ on a
finite alphabet is $D_f(P\|Q) = \sum_a Q(a) f(P(a)/Q(a))$ (Csiszár–Shields, *Information
Theory and Statistics: A Tutorial*, 2004, Section 4). The choices $f(t) = t\log t$,
$(t-1)^2$, $1 - \sqrt t$ and $|t-1|$ give the I-divergence, the $\chi^2$-divergence, the Hellinger
distance and the variational distance. Every f-divergence is nonnegative and decreases under
lumping (merging letters), the finite form of data processing. Here $Q$ is strictly positive and
$f$ is real-valued and convex on $[0, \infty)$.

- [f-divergence on a finite alphabet](f-divergence.md)
- [Lumping of a distribution along a map](lumping-of-a-distribution.md)
- [Generalised log-sum inequality](generalised-log-sum-inequality.md)
- [Lumping property of f-divergences](lumping-property-of-f-divergences.md)
- [Nonnegativity of f-divergences](nonnegativity-of-f-divergences.md)
- [The I-divergence is the f-divergence of $t \log t$](i-divergence-as-an-f-divergence.md)

## Related topics

- [Log-sum inequality](../sum-mul-log-sum-div-sum-le-sum-mul-log-d.md): the case $f(t) = t\log t$ of the
  generalised log-sum inequality.
- [Data-processing inequality](../data-processing-inequality/README.md): data processing for mutual
  information; the lumping property is its counterpart for f-divergences under deterministic maps.
- [Strong data processing and Dobrushin's coefficient](../strong-data-processing-and-dobrushin-s-coefficie/README.md):
  contraction coefficients of Markov kernels for total variation, the f-divergence of $\frac12|t-1|$.
- [I-projections](../i-projections/README.md): minimisation of the I-divergence, the f-divergence of
  $t\log t$, over convex sets.
