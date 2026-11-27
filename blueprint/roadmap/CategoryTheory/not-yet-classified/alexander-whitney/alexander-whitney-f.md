# Degree formula for the Alexander–Whitney map

Let `C` be a preadditive monoidal category with biadditive tensor product and finite
coproducts, and let `A` and `B` be simplicial objects in `C`. Write `C_*(A)` and
`C_*(B)` for their alternating-face chain complexes. For every natural number `n`,
the degree-`n` component of the Alexander–Whitney chain map
`C_*(A ⊗ B) → C_*(A) ⊗ C_*(B)` is

$\operatorname{AW}_{A,B,n}=\sum_{p=0}^{n}
(A([0,p]\hookrightarrow[n])\otimes B([p,n]\hookrightarrow[n]))\gg\iota_{p,n-p}.$

The two simplicial maps select the front vertices `0,…,p` in `A` and the back
vertices `p,…,n` in `B`. The morphism `ι_{p,n-p}` includes
`A_p ⊗ B_{n-p}` into the degree-`n` term of the tensor chain complex; `≫` denotes
composition in that order. The category's object and morphism universes are independent.
