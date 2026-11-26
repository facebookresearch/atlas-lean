# The stage map preserves the next-stage submodule

Let R be a commutative ring and M, N, M', N' R-modules. Let f.map : M × N →ₗ[R] M' × N' and
f.first : M →ₗ[R] M' satisfy f.map ∘ inl = inl' ∘ f.first. Put f.relative = snd' ∘ f.map ∘
inr. For every m, q : ℕ, nextStage R M N m q ≤ (nextStage R M' N' m q).comap (f.stageMap m q).
Thus the restricted exterior map sends the next stage inside the source stage to the
corresponding next target stage.
