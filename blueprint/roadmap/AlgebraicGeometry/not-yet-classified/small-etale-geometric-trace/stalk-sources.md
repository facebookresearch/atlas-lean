# Stalk Sources

Stalk data for the cohomology data `S`, where $\Omega$ ranges over algebraically closed fields:
for every scheme $X$, geometric point $p : \operatorname{Spec} \Omega \to X$ and primitive $l$-th
root of unity $\zeta \in \Omega^\times$, with $l$ invertible in $\Omega$, Tate coordinates at $p$
for $\zeta$ (`TateCoordinates`); for every morphism $f : Y \to X$, geometric point $p$ of $X$, lift
$s$ of $p$ to $Y$ and étale sheaf $F$ on $Y$, a map from the stalk of $f_*F$ at $p$ to the stalk of
$F$ at $s$ sending the germ at a lift $t$ of $p$ to an étale $U \to X$ of each section of $F$ over
$U \times_X Y$ to its germ at the induced lift $(t, s)$ (`StalkProjection`); and, for $f$ finite,
finiteness of the set of lifts of $p$ to $Y$.
