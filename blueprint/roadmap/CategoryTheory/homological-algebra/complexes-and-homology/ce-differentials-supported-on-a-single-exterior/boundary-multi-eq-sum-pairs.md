# A pure exterior word has the strict-pair bracket-and-deletion boundary

Let R be a commutative ring, L an R-Lie algebra and E = ExteriorAlgebra R L. Let ∂ be the CE
boundary with ∂(x∧y) = −[x,y]. For v : Fin n → L, ∂(ιMulti v) is ∑ i,j : Fin n with i<j, (−1 :
R)^(i+j) • (ι([v_i,v_j]) * product of the remaining ordered generators). The remaining list is
(List.ofFn v).eraseIdx j then eraseIdx i, so the larger index is removed first.
