# Frobenius Model

A Frobenius on the Nygaard-completed twists `T`: maps of complexes $\varphi_i$ from
`T.nygaard i` to `T.complex i`, for $i \in \mathbb{Z}$, such that every basis object $B$ has a
morphism $B \to C$ to a basis object $C$ with coordinates (`Context`) whose ring map is a
quasisyntomic cover, together with, for every basis object with coordinates `F` and every $i$, a
realization of the coordinate complexes (`Realization`) whose source map followed by $\varphi_i$
(evaluated at the basis object) is homotopic to the signed divided Frobenius `phiSigned` of the
coordinates followed by its target map.

These conditions constrain $\varphi_i$ only through its composites with the source maps of the
realizations, which are defined on the uncompleted coordinate complexes (the Nygaard steps of the
initial prism), whereas `T.nygaard i` and `T.complex i` are Nygaard-completed.
