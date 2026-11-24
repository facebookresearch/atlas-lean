# Of eq iff

For a semiring `R`, let `g₁ : GL (Fin n₁) R` and `g₂ : GL (Fin n₂) R`.
The classes `StableGL.of g₁` and `StableGL.of g₂` are equal if and only if there is a rank
`k ≥ n₁, n₂` at which the images of `g₁` and `g₂` under the two stabilization transitions
of `finiteGLDiagram` are equal in `GL (Fin k) R`.
