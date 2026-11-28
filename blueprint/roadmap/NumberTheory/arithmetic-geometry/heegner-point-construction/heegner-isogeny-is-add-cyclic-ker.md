# The Heegner isogeny is cyclic of degree `N`

Let `K ⊂ ℂ` be an imaginary quadratic field,
embedded by `σ : K →+* ℂ`, with ring of integers `𝓞 K`, and let `𝒩` be a nonzero ideal of `𝓞 K`
such that `𝓞 K ⧸ 𝒩` is cyclic of order `N`. Let `𝒩⁻¹ = {x ∈ K : x 𝒩 ⊆ 𝓞 K}` (Mathlib's inverse
of fractional ideals, `FractionalIdeal.mem_inv_iff`). Then `σ(𝓞 K)` and `σ(𝒩⁻¹)` are lattices in
`ℂ` (discrete `ℤ`-submodules spanning `ℂ` over `ℝ`) with `σ(𝓞 K) ⊆ σ(𝒩⁻¹)`, the quotient
`σ(𝒩⁻¹) / σ(𝓞 K)` is cyclic of order `N`, and the map `ℂ / σ(𝓞 K) → ℂ / σ(𝒩⁻¹)` induced by the
identity of `ℂ` is surjective with kernel `σ(𝒩⁻¹) / σ(𝓞 K)`, cyclic of order `N`.

Here `𝓞 K` is the unit fractional ideal `1`, and an isogeny of complex tori is expressed by the
surjective group homomorphism of the quotients with finite kernel; the complex structure of the
tori is not stated.

## Sources

- R. L. Miller, *Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic curves of analytic rank zero and one*, LMS J. Comput. Math. 14 (2011), 327–350, §4, p. 335 ("Since $\mathcal{O}_K \subset \mathcal{N}^{-1}$, we have a cyclic $N$-isogeny $\mathbb{C}/\mathcal{O}_K \to \mathbb{C}/\mathcal{N}^{-1}$ of elliptic curves with CM by $\mathcal{O}_K$"); B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989), London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256, §1, p. 235 (the complex tori $\mathbb{C}/\mathcal{O}$ and $\mathbb{C}/\mathcal{N}^{-1}$ "define elliptic curves related by a cyclic $N$-isogeny").
