# The forgotten-module augmented bar is a functor of algebras

For a monad T on C, define T.Algebra → SimplicialObject.Augmented C by alg ↦
emUnderlyingAugmented(alg) and φ ↦ emUnderlyingHom(φ). Its degree-n term has carrier
T(T^n(alg.A)), and its target is alg.A. The algebra-bar map identities and composition laws
give functoriality.
