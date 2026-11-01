---
article_id: af_2135760803f8578ce9478ff7
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.genocchiPowerSeries
---

# Genocchi Power Series

Exponential generating function of the Genocchi numbers `Gₙ`:
`2 * x / (exp x + 1) = ∑ₙ Gₙ * x ^ n / n!`.

This retains the standard `2 * x / (exp x + 1)` convention stated by Chen and
used independently by Kida; the sign-changed variant consumes only even-index
terms, where the conventions agree.

Provenance:
- phrase concept `jis_term_2151ebeb03d46b7f51d94f94`
- source statements `jis_21afe12570e34775c299908d` and `jis_5d32bc9f1d45c583ec9b9547`
- Chen, JIS VOL6 (`JIS VOL6/Chen/chen50.tex`, lines 296-300, duplicated in
  `chen53.tex`): https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen50.html
- Kida, JIS VOL16 (`JIS VOL16/Kida/kida2.tex`):
  https://cs.uwaterloo.ca/journals/JIS/VOL16/Kida/kida2.html

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.GenocchiNumber](../../../../../sources/v2/MathlibExt.md)
