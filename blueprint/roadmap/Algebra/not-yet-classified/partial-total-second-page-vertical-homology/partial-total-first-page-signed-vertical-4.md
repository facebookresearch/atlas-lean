# Partial Total First Page Signed Vertical Homology Component Iso

Let $C$ be an abelian category and let $B$ be a double chain complex in $C$
indexed by $\mathbb N$ in both directions. For $p,q\in\mathbb N$, let
$E^1_B(p,q)$ be the first-page term of its partial-total spectral sequence
with the increasing homological indexing convention
`coreE₁IncreasingHomologicalNat`.

There is a canonical isomorphism

$$
E^1_B(p,q)\cong H_q(B.X(p)).
$$

It is the composite of `partialTotalSpectralSequenceFirstPageRowIso p q`
with `totalRowHomologyIso p q`. The target is the $p$th object of
`signedVerticalHomologyComplex q`: its horizontal differential from $p$ to
$p'$ is $\varepsilon(q)$ times the homology map induced by $B.d(p,p')$, with
$\varepsilon(q)$ the sign of `ComplexShape.down ℕ`. Thus the component uses
the vertical homology objects with the signed horizontal differential.
