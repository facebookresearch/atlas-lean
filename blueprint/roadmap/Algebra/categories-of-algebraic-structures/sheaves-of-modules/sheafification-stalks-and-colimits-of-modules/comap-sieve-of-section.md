# Membership sieve of a submodule preimage

Let `R` be a presheaf of rings on `C`, `f : M → P` a module-presheaf morphism, `N≤P` a
submodule presheaf, `X : Cᵒᵖ`, and `x∈M(X)`. The sieve of arrows along which `x` restricts
into `N.comap f` equals the sieve along which `(f.app X)(x)` restricts into `N`: `(N.comap
f).toSubfunctor.sieveOfSection x = N.toSubfunctor.sieveOfSection ((f.app X) x)`.
