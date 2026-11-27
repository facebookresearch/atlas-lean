# Stage Two Extraction

Let `C` have a zero object and a Waldhausen structure without gluing.
The functor `Stage C 2 ⥤ CofiberSequenceCategory C` sends a stage diagram
`A` to its three values `A(0,1) ⟶ A(0,2) ⟶ A(1,2)`. Write
`h01 : (0 : Fin 3) ≤ 1` and `h12 : (1 : Fin 3) ≤ 2` for the order proofs.
Its two legs are `A.obj.map (horiz h01 h12)` and
`A.obj.map (vert h01 h12)`. A stage morphism `φ` is sent to the three
components of `φ.hom` at `interval 0 1 h01`, `interval 0 2 (h01.trans h12)`,
and `interval 1 2 h12`, with the two naturality squares. Here `A(i,j)`
denotes the value of `A.obj` on the interval `(i,j)`. This is extraction
of the supplied diagram, not a claimed inverse or equivalence.
