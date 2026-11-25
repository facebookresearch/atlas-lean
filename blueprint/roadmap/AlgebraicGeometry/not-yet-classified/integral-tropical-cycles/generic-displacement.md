# Generic Displacement

A displacement `v` is generic at `w` if it avoids the direction sum of every pair of cells of
the weighted supports through `w` whose directions do not span the whole space. Only cells inside
the weighted supports (nonzero-weighted facets and their faces) count: a cell of weight zero
outside the supports does not constrain the displacement, while a face of a weighted facet, such as
a new vertex of a subdivision, still does.
