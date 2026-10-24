---
article_id: af_498c4851786229a20f574869
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.carnot_inradius_circumradius_general
---

# Carnot inradius circumradius general

Carnot's theorem (inradius, circumradius), general form: for a nondegenerate triangle with
    circumcenter `O`, circumradius `R`, incenter `I`, and inradius `r`, the signed
    distances `x`, `y`, `z` from `O` to the three sidelines (each measured with an
    inward unit normal, hence positive toward the opposite vertex) satisfy
    `x + y + z = R + r`.
    Source: https://en.wikipedia.org/wiki/Carnot%27s_theorem_(inradius,_circumradius).
    Statement ID: carnot-inradius-s1.

Unlike `carnot_inradius_circumradius`, this drops the hypotheses `O ∈ affineSpan ℝ {A, B, C}`
    and `0 < r`, which the proof never needs.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.CarnotInradius](../../../../../../sources/v2/MathlibExt.md)
