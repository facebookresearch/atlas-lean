# Currying commutes with postcomposition in the target module

Currying commutes with postcomposition in the target module.

For `f : A ⊗_R B ⟶ C` and `g : C ⟶ C'`, currying `f ≫ g` equals the curried map of `f`
followed by the Hom functor's image of `g`.
