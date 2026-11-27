# A pure enveloping tensor multiplies only the endpoints

Let `k` be a commutative semiring and `A` a `k`-algebra whose underlying multiplication may be
noncommutative. Put `E=A ⊗[k] Aᵐᵒᵖ` and `X_n=A ⊗[k] TensorPower k (n+1) A`. For `l,r,a₀ : A`
and `a : Fin(n+1) → A`, `(l⊗op(r)) • (a₀⊗tprod(a)) = (l*a₀) ⊗ tprod(Fin.snoc (Fin.init a)
(a(Fin.last n)*r))`. The right scalar multiplies after the final factor.
