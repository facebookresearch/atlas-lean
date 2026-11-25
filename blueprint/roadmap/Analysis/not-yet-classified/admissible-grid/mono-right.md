# Mono right

Admissibility persists when the ambient set is enlarged.

```lean
theorem IsAdmissibleFor.mono_right {D : GridFilling} {K G H : Set ℂ}
    (hD : D.IsAdmissibleFor K G) (hGH : G ⊆ H) : D.IsAdmissibleFor K H
```
