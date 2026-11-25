# Native general thom isomorphism

Thom isomorphism: let $k$ be a perfect field, and fix the given motivic interface data, whose
affine-to-Tate comparison has the properties of the canonical one (`CanonicalAffineSource`).
Let $X$ be a smooth $k$-scheme, $G$ a rank-$d$ bundle geometry on a sheaf of modules on $X$ with
chosen bundle diagonals $Δ$ (`BundleThomDiagonals`), $t$ a Thom class of $G$ and $U_0$ a chosen
coefficient identification. Then for every pointed space $W$, all $p, q ∈ ℤ$ and every abelian
group $A$, the Thom action $u ↦ Δ^*(u ∪ t)$ (`thomAction`) from $\tilde H^{p,q}(W ∧ X_+; A)$ to
$\tilde H^{p+2d,q+d}(W ∧ \mathrm{Th}(G); A)$ is bijective.
