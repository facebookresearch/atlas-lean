---
article_id: af_9c5c2985d9386edf82c8a7fc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.SchwarzPick.schwarzPick
---

# Schwarz Pick

If `f : ℂ → ℂ` is holomorphic on `ball 0 1` and maps the ball into itself, then `‖(f z - f w)/(1 -
conj (f w) * f z)‖ ≤ ‖(z - w)/(1 - conj w * z)‖` for all `z, w ∈ ball 0 1`, where `conj = star`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.SchwarzPick](../../../../../../sources/v2/MathlibExt.md)
- Schwarz–Pick lemma, G. Pick (1916), building on Schwarz's lemma; see Ahlfors; Lean is holomorphic self-map of disc pseudo-hyperbolic distance nonincreasing inequality with star conj. Proves `Wanted` entry `schwarzPick`.
