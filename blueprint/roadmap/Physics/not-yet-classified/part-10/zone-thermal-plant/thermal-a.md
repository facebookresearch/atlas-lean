# Thermal A

State matrix of the zone network, acting on the vector of zone temperatures: row `i` is
zone equation `i` without its input terms, divided by `C i`, so entry `(i, j)` is
`(G i j - if i = j then (∑ k, G i k) + g0 i else 0) / C i` and the diagonal conductance
`G i i` cancels. Meaningful for `C i > 0`; at `C i = 0` the totalized division makes row `i`
zero. Without self-links the inner matrix is the negative of
`PhyslibExt.Mechanics.HarmonicMechanics.stiffnessMatrix G g0`; here `G i i`
cancels, while there it stays on the diagonal.
