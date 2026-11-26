# Balanced induction and tensor scalar extension agree

Let `k : Type u` and `R : Type v` be commutative rings, `φ : k →+* R`, and `w` a
carrier-universe parameter. There is a natural isomorphism `ModuleCat.induceScalars.{u,v,w} φ
≅ ModuleCat.extendScalars.{u,v,max u v w} φ`, on modules of universe `max u v w`. It is
induced by the two induction/extension adjunctions with the same restriction-of-scalars
functor.
