# Tensor-word formula for the signed shuffle product

Let `k` be a commutative ring and `V` a `k`-module.
Write `Sh(p,q)` for permutations that place two ordered blocks
of lengths `p,q`, and `ε(s)` for the integer sign of the shuffle. For words `a : Fin p → V`, `b : Fin q → V`, the product is
`∑_(s∈Sh(p,q)) ε(s) • tprod_k(i ↦ append(a,b)(s⁻¹(i)))` on
`tprod_k(a) ⊗ tprod_k(b)`.
