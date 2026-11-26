# Preserving

Strong finite-tensor-preserving functor.

The comparison is oriented as
`map F ⋙ tensor_W ≅ tensor_V ⋙ F`, i.e. the tensor of `F`-images is
identified with `F` of the tensor. The two coherences are the
pseudoalgebra morphism laws for the finite-family monad, expressed
with the existing `singletonMapIso`, `flattenMapIso`, `mapIso`,
`mapCompIso` as the explicit functor-composition coherence,
`isoWhiskerLeft` and `isoWhiskerRight` APIs.
