# Same Label Tree

Given an original cell tree `O`, chosen lower-set colimits `M`, regular
`chi`, working-size colimits in `C`, and a complete compatible history `H`,
assemble a cell tree on the same carrier `P` with the refining order
`sameLabelOrder`. Its label at `p` is `O.label p` (`sameLabelTree_labels`).

Sharing the original objects means sharing that index carrier and those
labels, not that the `Under X` vertex values agree with `O`'s. The vertices
are related by `sameLabelComparison`, a natural transformation from the new
diagram to `O.diagram` pulled back along the monotone identity `sameLabelHom`
from the new order to the old one. The endpoint comparison
`sameLabelEndpointIso` is an isomorphism in `Under X` from the new endpoint
to `O.endpointObj`, with `new.hom ≫ endpointIso.hom.right = O.hom`
(`sameLabelEndpoint_root`).
