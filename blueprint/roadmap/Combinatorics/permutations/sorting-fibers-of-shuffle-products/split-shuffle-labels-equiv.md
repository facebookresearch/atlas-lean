# A shuffle splits a labeling into two blocks

Let `p,q,m : ℕ` and `s : Shuffle p q`. The equivalence `(Fin(p+q) → Fin m) ≃ (Fin p → Fin m) ×
(Fin q → Fin m)` sends `f` to `g(i)=f(s.perm(Fin.castAdd q i))` and `h(j)=f(s.perm(Fin.natAdd
p j))`. Its inverse assigns `g` and `h` to the corresponding value blocks using `s.perm⁻¹`.
