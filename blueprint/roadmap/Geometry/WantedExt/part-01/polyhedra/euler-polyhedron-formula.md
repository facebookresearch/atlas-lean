---
article_id: af_c0897355c43982e4a8b4ba8b
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.euler_polyhedron_formula
---

# Euler Polyhedron Formula Wanted

Euler's polyhedron formula (statement `euler-polyhedron-s1`, canonical name
"Euler's polyhedron formula") for a supplied finite polygonal cellulation of the
boundary of a three-dimensional convex polyhedron: if the cellulation has `V`
vertices, `E` edges, and `F` faces, then `V - E + F = 2`.

Here `P` is the convex hull of all embedded cellulation vertices in
`EuclideanSpace Real (Fin 3)` and has nonempty interior. The vertex set `V`
may include non-extreme subdivision vertices, for instance vertices introduced
along an edge or inside an exposed face, so no hypothesis requires every
embedded vertex to be an extreme point of `P`. The remaining hypotheses encode
the incidence data of a boundary cellulation: listed edges are atomic (they
contain no listed vertex in their relative interior), distinct listed edges
meet only at a shared endpoint, each listed edge lies in exactly two listed
faces, the faces cover the frontier and meet only along listed vertices or
edges, and each face has the stated boundary incidence. Edge completeness is
imposed only on atomic boundary segments. The data may describe a subdivision
of an exposed polyhedron face (for example by adding a diagonal); the theorem
concerns the resulting cellulation and does not claim that `E` and `F` are
exactly the maximal exposed edges and faces of `P`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Geometry.Polyhedra.EulerPolyhedronFormulaWanted](../../../../../sources/v2/WantedExt.md)
- https://en.wikipedia.org/wiki/Euler_characteristic.
