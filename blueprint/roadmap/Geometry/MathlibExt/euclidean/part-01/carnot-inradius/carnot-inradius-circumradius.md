---
article_id: af_5e9b59c7508992dddf05f410
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.carnot_inradius_circumradius
---

# Carnot inradius circumradius

Carnot's theorem (inradius, circumradius): for a nondegenerate triangle with
    circumcenter `O`, circumradius `R`, incenter `I`, and inradius `r`, the signed
    distances `x`, `y`, `z` from `O` to the three sidelines (each measured with an
    inward unit normal, hence positive toward the opposite vertex) satisfy
    `x + y + z = R + r`.
    Source: https://en.wikipedia.org/wiki/Carnot%27s_theorem_(inradius,_circumradius).
    Statement ID: carnot-inradius-s1.

It follows from `carnot_inradius_circumradius_general`; the hypotheses `hOplane` and `hrpos`
    are unused and keep the `Wanted` statement's shape.
Proves `Wanted` entry `carnot_inradius_circumradius`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Carnot inradius circumradius general](carnot-inradius-circumradius-general.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.CarnotInradius](../../../../../../sources/v2/MathlibExt.md)
