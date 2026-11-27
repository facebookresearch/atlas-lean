# Vector field of the Levins model on a patch network

For a finite set `ι` of patches, a real matrix `C`, real rates `e_i` and `p ∈ ℝ^ι`, the vector field
is `F(p)_i = (1 − p_i) (C p)_i − e_i p_i`, with `(C p)_i = ∑_j C_ij p_j`. In the model,
`p_i ∈ [0, 1]` is the probability that patch `i` is occupied, an occupied patch `j` sends colonists
to patch `i` at rate `C_ij ≥ 0`, and the population of patch `i` goes extinct at rate `e_i > 0`; an
empty patch, of probability `1 − p_i`, is colonized at rate `(C p)_i`. The formula is defined for
all real inputs.
