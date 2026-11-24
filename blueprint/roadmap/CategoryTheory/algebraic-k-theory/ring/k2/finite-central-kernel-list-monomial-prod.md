# Stable Steinberg Finite Weyl Kernel Monomial

Finite central-kernel Weyl words have trivial monomial product: for
`g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n` over `[Field F]`,
there are `m`, endpoint functions `a b : Fin m → ℕ` with bounds `ha hb`,
distinctness `hab`, and units `u : Fin m → Fˣ` such that `g` is the head-left
`List.ofFn`/`List.prod` ordered product of the stable `weyl` generators and the
corresponding ordered product of the accepted `weylMonomialSLUnit` terms at
`⟨a k, ha k⟩`, `⟨b k, hb k⟩` equals `1`. `[Field F]` is required by the
`bruhatMiddle` retraction in the proof. The empty list gives `1 = 1`. Purpose:
central-kernel monomial input. Nonclaims: no finite-torus containment, torus
landing, well-definedness across representations, kernel generation, TWT, or
Matsumoto claim.
