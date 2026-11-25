# Diagonalizable states

A state `φ` on `B(ℓ²)` is diagonalizable: `φ(T) = lim_{k → U} ⟨T eₖ, eₖ⟩` for some orthonormal
basis `(eₖ)` of `ℓ²` and some ultrafilter `U` on `ℕ` (Mathlib's inner product is conjugate-linear
in the first argument, so `⟨T eₖ, eₖ⟩` is `inner ℂ (e k) (T (e k))`).
