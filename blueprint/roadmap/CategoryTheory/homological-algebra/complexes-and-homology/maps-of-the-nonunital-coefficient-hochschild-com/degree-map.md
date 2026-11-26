# The algebra and coefficient maps act factorwise on each tensor degree

Let k be commutative, A and B nonunital k-algebra rings, M and N k-modules, g : A →ₙₐ[k] B and
f : M →ₗ[k] N. For n : ℕ, degreeMap g f n : M ⊗[k] TensorPower k n A →ₗ[k] N ⊗[k] TensorPower
k n B is TensorProduct.map f (PiTensorProduct.map (fun _ => g)).
