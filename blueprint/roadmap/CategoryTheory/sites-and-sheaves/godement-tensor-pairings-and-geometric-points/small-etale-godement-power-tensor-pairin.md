# Tensor pairing of arbitrary Godement monad powers

Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For n ∈ ℕ, the iterated pairing is
m_n : T^n(F) ⊗_sheaf T^n(H) → T^n(F ⊗_sheaf H).
It starts with m₀ = id and obeys
m_(n+1)(F,H) = T^n(m₁(F,H)) ∘ m_n(T(F),T(H)).
