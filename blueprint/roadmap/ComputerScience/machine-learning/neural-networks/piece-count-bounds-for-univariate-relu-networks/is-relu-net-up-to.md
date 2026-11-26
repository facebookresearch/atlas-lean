# ReLU networks up to a layer

A ReLU network up to layer `n`: layers `0, ..., n - 1` apply `posPart`
coordinatewise after an affine map. These are exactly the layers that
`forward n` traverses.
