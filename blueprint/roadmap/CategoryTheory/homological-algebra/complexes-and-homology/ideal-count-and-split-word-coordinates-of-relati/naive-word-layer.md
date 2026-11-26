# The naive word layer is the quotient by its predecessor inside the stage

Let k be a commutative ring, A a nonunital ring with a k-module structure and k-bilinear
multiplication, and I a two-sided nonunital k-subalgebra. Put Q = A/I. Write K_b =
ker(bComplex(A) → bComplex(Q)), and identify its degree-n inclusion with an injective word map
W_n : (K_b)_n → A^⊗(n+1). naiveWordLayer p n is F_p ⧸ (F_lower.comap F_p.subtype), where F_p =
naiveWordFiltration p n and F_lower = naiveLowerFiltration p n.
