# Glued degree-zero Picard group

The admissible gluing data modulo the glued principal
data, for a finite set `S` of pairs `(P_s, Q_s)` of `K`-rational places of `F`.

Interpretation: when `F` is the function field of a smooth projective curve `C` over `K` and the
places in each projection of `S` are distinct, gluing two copies `C₁` and `C₂` of `C` by
identifying `P_s ∈ C₁` with `Q_s ∈ C₂` gives a curve `X` with a node at each glued point. Then `D₁`
and `g₁` live on `C₁`, `D₂` and `g₂` live on `C₂`, and the group models the line bundles on `X` of
degree zero on each component, with `toPic0Pair` as restriction to `C₁` and `C₂`. This
identification is an interpretation: the definition refers to no curves or line bundles, and
applies to any field extension `F` of `K` and any such `S`.
