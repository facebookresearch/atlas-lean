# If $x, x+v \in D$ with $Av = 0 \ne v$, the law is not injective on $D$

Let the rays and the attenuation cells form finite sets, let $A$ be a real matrix indexed by rays
and cells, let the source intensities $I_{0,j}$ be any nonnegative numbers (positivity is not
needed), and let $D$ be a set of attenuation vectors. If a vector $v \ne 0$ satisfies $Av = 0$ and
some $x$ has both $x$ and $x + v$ in $D$, then the map $x \mapsto P_x$ sending an attenuation vector
to its [photon-count law](photon-law.md) is not injective on $D$: the distinct vectors $x$ and
$x + v$ have the same law. Such a $v$ exists when the rank of $A$ is less than the number of cells,
as for the [single ray through two cells](ct-row.md).
