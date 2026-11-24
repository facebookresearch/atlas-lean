# Edge Volume

Edge volume of the path flow `f` on the supplied routes `edges`: every traversal counts,
`edgeVolume edges f e = ∑ p, f p * (edges p).count e`, in the flow unit of `f`. The
vertex-pair analogue for canonical paths between states is
`MathlibExt.Probability.CanonicalPaths.pathLoad`; here arcs are told apart by identity
and every traversal counts.
