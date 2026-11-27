# Exterior semilinear maps respect scalar composition

Let `R,S,T` be commutative rings, `M,N,P` respectively modules over them, `φ : R →+* S`, `ψ :
S →+* T`, `f : M →ₛₗ[φ] N`, and `g : N →ₛₗ[ψ] P`. With composite scalar map `ψ.comp φ` and its
`RingHomCompTriple` compatibility, `(mapSemilinear ψ g n).comp (mapSemilinear φ f n) =
mapSemilinear (ψ.comp φ) (g.comp f) n` for every `n : ℕ`.
