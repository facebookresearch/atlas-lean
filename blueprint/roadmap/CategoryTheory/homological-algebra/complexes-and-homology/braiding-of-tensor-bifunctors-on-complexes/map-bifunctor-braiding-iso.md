# Cellwise braiding compares tensor and flipped-tensor bicomplexes

Let C be a preadditive monoidal category with tensor product additive in both variables, and
assume C is braided. Let c₁ and c₂ be arbitrary complex shapes on independent index types, K a
c₁-complex and L a c₂-complex. mapBifunctorBraidingIso compares the bicomplex with cells K_p ⊗
L_q to the one with cells L_q ⊗ K_p, both of shape (c₁,c₂). Its cell (p,q) forward map is
β_(K_p,L_q).hom and inverse map is β_(K_p,L_q).inv; braiding naturality gives both
differential squares.
