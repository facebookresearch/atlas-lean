# Native finite bundle cycle class

Voevodsky, Construction 5.1 (class of a finite relative cycle): let $k$ be a perfect field,
and fix the given motivic interface data, whose affine-to-Tate comparison has the properties of
the canonical one (`CanonicalAffineSource`). Let $X$ be a smooth $k$-scheme, $G$ and $G_L$
bundle geometries of ranks $d$ and $e$ on sheaves of modules $M$ and $L$ on $X$, $G_S$ one of
rank $n = d + e$ on $M ⊕ L$ with a chosen frame $φ : M ⊕ L ≅ \mathcal{O}_X^n$, $C_G$ given cycle
geometry data for every relative generator of $G$ (`CycleGeometry`), $Δ$ chosen bundle
diagonals of $G_L$, $t$ a Thom class of $G_L$, $U_0$ a chosen coefficient identification, $A$ an
abelian group and $z$ a finite relative cycle on $G$ with coefficients in $A$ whose coefficient
section vanishes on the complement of the zero section of $G_L$ (`ComplementNull`). Then: a
class $u ∈ \tilde H^{2d,d}(X_+; A)$ whose image under the Thom action of $t$ is the finite Thom
class of $z$ (`IsFiniteBundleCycleClass`).
