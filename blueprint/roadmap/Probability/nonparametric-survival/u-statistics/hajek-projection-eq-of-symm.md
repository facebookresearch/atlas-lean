# Hajek Projection eq of symm

Assume `∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y`.

For a symmetric kernel the symmetrization in `hajekProjection` is the identity, so the
projection is `θ + (m / n) ∑_{i} (h₁(x_i) - θ)` with `h₁ = hoeffdingProj μ h 1`.
