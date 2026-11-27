# Higher tensor representatives are natural across algebra carrier universes

Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Let B : Type w be another k-algebra ring and f : A
→ₙₐ[k] B a nonunital k-algebra map. Use the common height H = max u v w z and let Cλ_H(f) be
the induced map between the two quotient complexes. For n : ℕ and x : TensorPower k (n + 1) A,
Cλ_H(f)_n(q_H^A(x)) = q_H^B(PiTensorProduct.map (fun _ => f) x). Thus every tensor factor is
mapped by f.
