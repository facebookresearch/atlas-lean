# Cell Tree

A labelled cell tree on a vertex carrier `P` over a root `X`.

The strict order on `P` is well founded; it is not required to be linear, and
strict-predecessor sets are not assumed discrete. The data is a diagram
`P ⥤ Under X`, a label `P → α` naming the attaching arrow `s (label a)` of
each vertex `a`, a chosen colimit cocone of the diagram restricted to
`LowerSet.Iio a` at every `a`, an attaching map from `(s (label a)).left` into
the underlying object of that predecessor colimit, and a cell map from
`(s (label a)).right` into the underlying object of the vertex. At every `a`
those exhibit the vertex as the pushout of `s (label a)` along the attaching
map, over the predecessor-to-vertex map. A chosen colimit cocone of the whole
diagram is part of the data.
