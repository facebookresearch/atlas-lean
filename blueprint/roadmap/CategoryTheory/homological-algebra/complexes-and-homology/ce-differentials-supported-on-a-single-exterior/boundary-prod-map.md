# The CE boundary of an ordered generator list is its signed strict-pair sum

Let R be a commutative ring, L an R-Lie algebra and E = ExteriorAlgebra R L. Let ∂ be the CE
boundary with ∂(x∧y) = −[x,y]. For xs : List L, ∂(product(xs.map ι)) is the sum over i<j in
Fin xs.length of (−1 : R)^(i+j) times ι([xs_i,xs_j]) followed by the product of xs with index
j then i erased. Empty and one-entry lists have an empty pair sum.
