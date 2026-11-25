# Arinkin's autoduality kernel for compactified Jacobians

Let $k$ be an algebraically closed
field of characteristic zero and $C$ an integral proper curve over $k$ with planar singularities
(the cotangent space at every closed point has dimension at most $2$), with its torsion-free
restrictions to subcurves (`TorsionFreeRestrictions`); let $q$ be a polarization of total weight
$1 - g$, where $g = \dim_k H^1(C, \mathcal{O}_C)$, $s$ a smooth marking and $\bar J$ a fine
compactified Jacobian for $q$ and $s$, and assume that derived pullbacks, pushforwards and tensor
products exist (`HasDerivedPullbacks`, `HasDerivedPushforwards`, `HasDerivedTensors`). Then there is
a Poincaré-kernel candidate on $\bar J \times \bar J$ (`PoincareKernelCandidate`) that has Arinkin's
geometric properties (`Properties`, Theorems A and B) and is a Fourier–Mukai autoduality kernel
(`IsAutodual`, Theorem C).
