# Tensor Obj X eq graded

The carrier of a complex tensor product is the graded tensor product.

Rewrite direction: from `(tensorObj K L).X` to
`GradedObject.Monoidal.tensorObj K.X L.X`.  Applying this once exposes one
tower layer; the contract test rewrites the carrier equality directly.
