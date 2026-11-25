# Homogeneous coordinates distinguish points from vectors

The homogeneous action distinguishes points from
vectors: on extended coordinates `Sum.elim q (fun _ => w)`,
the homogeneous matrix acts as
`Sum.elim (R *ᵥ q + w • p) (fun _ => w)`. At `w = 1` this
is the point action `R *ᵥ q + p`; at `w = 0` the translation
vanishes, the vector action.
