# Functional delta theorem in `ℓ^∞((0, τ))`

**Functional delta theorem in `ℓ^∞([0, τ])`**, the shape of the continuous-time
Kaplan–Meier statement. Topology: the uniform (sup-norm) topology of `ℓ^∞([0, τ])`, tangent set
the continuous functions `C[0, τ]`, scale `r n = √n`. If `√n (Λ̂ₙ - Λ) ⇒ G` with continuous `G`
(`hCLT`, `hG`) and `prodInt` is Hadamard differentiable at `Λ` tangentially to `C[0, τ]` with
derivative `prodInt'` (`hHad`), then `√n (prodInt Λ̂ₙ - prodInt Λ) ⇒ prodInt' G`.

`Λhat`, `prodInt`, `prodInt'` and `dom` are arbitrary: nothing ties them to the Nelson–Aalen
estimator or a product integral, and the Hadamard differentiability of the continuous-time
product-integral map (van der Vaart §20.3) is **not proved here**. Moreover the
`AEMeasurable` fields of `hCLT` fail for the continuous-time Nelson–Aalen process on the
canonical space of the observations whenever the law of the uncensored observation times in
`[0, τ]` has a non-atomic part (the `n = 1` counterexample in the module docstring), so this
theorem does not apply to continuous-time Kaplan–Meier in that case; it applies when the
processes stay Borel measurable, e.g. in a separable subspace.
