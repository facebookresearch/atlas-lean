---
article_id: af_6714b73e8d7bb7a4aaf28f85
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.hilbert_bernays_lob_second_incompleteness
---

# Hilbert Bernays Lob

Purely abstract Hilbert–Bernays–Löb derivability schema. A theory `T` has an
internal provability operator satisfying the derivability conditions, an internal fixed
point for its own unprovability, and a consistency sentence
`Con = neg (Prov falseStmt)`. If `T` is consistent, it does not prove `Con`.

This declaration assumes the derivability and fixed-point interface rather than deriving
it from a concrete encoding of first-order arithmetic.

Proof: Derive the needed implicational combinators from K and S, apply D1–D3 to the Gödel
fixed point, and contrapose `Prov G → Prov falseStmt`. This is the Hilbert–Bernays–Löb route
of Hilbert–Bernays (1939) and Löb (1955), as presented by Boolos, Ch. 3, and Smith, Ch. 33.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Logic.HilbertBernaysLob](../../../sources/v2/MathlibExt.md)
- Kurt Gödel, *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I*, Monatshefte für Mathematik und Physik 38 (1931), 173–198; Martin H. Löb, *Solution of a problem of Leon Henkin*, Journal of Symbolic Logic 20 (1955), 115–118.
