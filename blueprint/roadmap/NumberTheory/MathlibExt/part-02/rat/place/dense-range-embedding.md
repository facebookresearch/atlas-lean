---
article_id: af_886b425e242149e1fa49be32
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Rat.Place.denseRange_embedding
---

# Dense Range embedding

The image of `ℚ` is dense in each completed field `ℚ_v`.

Uses `Rat.denseRange_cast (𝕜 := ℝ)` at infinity and
`Padic.denseRange_ratCast p` under the local `Fact` at finite primes.

## Depends on

- [Place](place.md)
- [Completed Field](completed-field.md)
- [Completed Field Bundle](completed-field-bundle.md)
- [Bundle](bundle.md)
- [Embedding](embedding.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Rat.Place](../../../../../../sources/v2/MathlibExt.md)
