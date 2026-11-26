# The tensor-coefficient chain-complex functor

Let R : Type u be a commutative ring and K a chain complex in ModuleCat.{v} R indexed by ℕ.
Define a functor ModuleCat.{t} R → ChainComplex(ModuleCat.{max(v,t)} R,ℕ) by M ↦ M⊗_R K. Its
degree-n object is M⊗_R K_n, its differential is id_M⊗d_K, and a coefficient map acts on the
first factor. No flatness is needed to define the functor.
