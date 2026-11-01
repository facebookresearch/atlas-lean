---
article_id: af_b089d910cbd4a82d00e0517e
declaration: structure
origin: cited
statement: formalized
lean: MetaMathlibExt.TripSternTree
---

# Trip Stern Tree

The TRIP-Stern tree for a fixed pair of source transitions induced by `F_0`
and `F_1`: a distinguished root seed together with a fixed left transition and
a fixed right transition on node values. A left edge is represented by `false`
and a right edge by `true`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.TripSternTree](../../../../../sources/v2/MathlibExt.md)
- Ilya Amburg, Krishna Dasaratha, Laure Flapan, Thomas Garrity, Chansoo Lee, Cornelia Mihaila, Nicholas Neumann-Chun, Sarah Peluse, and Matthew Stoffregen, *Stern Sequences for a Family of Multidimensional Continued Fractions: TRIP-Stern Sequences*, Journal of Integer Sequences 20 (2017), Article 17.1.7, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Garrity/garrity6.tex>. The tree abstracts Definition TRIPSternDef, lines 471-481 (seed (1,1,1), even/odd recursion by F_0/F_1, levels as index intervals), with F_0/F_1 from line 387; binary paths follow the triangle(v) definition, lines 485-488.
