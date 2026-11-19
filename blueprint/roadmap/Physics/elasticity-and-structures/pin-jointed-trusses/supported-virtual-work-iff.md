# The principle of virtual work for a supported plane truss

Let a plane truss have finitely many joints $j$, at positions $r_j \in \mathbb{R}^2$, and finitely
many members $e$, joining the joints $a(e)$ and $b(e)$. Let $B$ be the compatibility matrix with rows indexed by
members and columns by joint coordinates, so that
$(Bu)_e = (r_{b(e)} - r_{a(e)}) \cdot (u_{b(e)} - u_{a(e)})$ for joint displacements $u$; let $S$
be a matrix from a finite set $F$ of free coordinates to joint coordinates; and let $s$ assign a real
coefficient $s_e$ to every member and $f \in \mathbb{R}^F$ be a load. Then

$$(BS)^{\top} s = f \iff s \cdot (BS)\,v = f \cdot v \ \text{ for every } v \in \mathbb{R}^F :$$

the member coefficients $s$ balance the supported load $f$ exactly when the internal virtual work
equals the external virtual work for every supported virtual displacement. For a member of positive
length $L_e$, $s_e$ is the axial force divided by $L_e$, tension positive; the test displacements
range over the free coordinates only, so support reactions are excluded.
