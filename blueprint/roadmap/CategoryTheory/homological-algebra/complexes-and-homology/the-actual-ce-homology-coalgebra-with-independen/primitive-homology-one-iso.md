# Primitive-complex degree-one homology is the lifted Lie module

Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. If Module.Free k L holds, primitiveHomologyOneIso identifies
(nativePrimitiveComplex k L).homology 1 with ModuleCat.of k (ULift.{u} L), by the
primitive-singleton chain isomorphism and its degree-one homology.
