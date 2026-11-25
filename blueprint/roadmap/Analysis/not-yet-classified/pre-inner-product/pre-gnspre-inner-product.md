# Positive semidefinite pre-GNS core

Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. For
`x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`. for
`e=preGNSLinearEquiv φ`, the core on `PreGNS φ` has `inner x y=P(e(x),e(y))`, Hermitian
symmetry, nonnegative real diagonal, additivity and conjugate linearity in the first argument.
