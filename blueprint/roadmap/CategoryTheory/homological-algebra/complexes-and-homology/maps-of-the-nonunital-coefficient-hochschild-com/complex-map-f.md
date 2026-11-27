# Every coefficient Hochschild chain component is the factorwise tensor map

Let k be a commutative ring, A and B nonunital k-algebra rings with k-bilinear multiplication,
and M and N k-modules. Equip M with commuting nonunital actions l_A : A →ₙₐ[k] End_k M and r_A
: Aᵐᵒᵖ →ₙₐ[k] End_k M, and N with commuting actions l_B and r_B. Let g : A →ₙₐ[k] B and f : M
→ₗ[k] N satisfy f(l_A(a)m) = l_B(g(a))f(m) and f(r_A(op a)m) = r_B(op(g(a)))f(m). For n : ℕ,
complexMap.f n = ModuleCat.ofHom (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n =>
g))).
