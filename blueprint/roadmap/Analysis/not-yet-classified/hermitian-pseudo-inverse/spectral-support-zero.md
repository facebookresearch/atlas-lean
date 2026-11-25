# Spectral Support zero

The spectral support of the zero matrix is zero.

The coefficient field is real or complex; `n` is any finite index type with decidable equality,
including an empty type.

```lean
theorem spectralSupport_zero : spectralSupport (0 : Matrix n n 𝕜) = 0
```
