# The comparison between iterated powers of two monads

Let C be a category and h : T → S a monad morphism on C. Define natural transformations h^n :
T^n → S^n recursively by h^0=id and h^{n+1}=h horizontally composed with h^n. Here T^n and S^n
are monadPow at n. This is the comparison obtained by applying h to every one of the n monad
factors.
