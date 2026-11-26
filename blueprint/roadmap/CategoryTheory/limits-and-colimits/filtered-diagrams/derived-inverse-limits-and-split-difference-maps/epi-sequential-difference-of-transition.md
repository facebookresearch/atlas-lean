# Sequential difference is surjective for surjective transitions

Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R`. Assume every successor transition
`τ_n=A.map (homOfLE (Nat.le_succ n)).op : A_{n+1} → A_n` is epi. Then `sequentialDifference A
: ∏ A_n → ∏ A_n`, with coordinate `a_n - τ_n(a_{n+1})`, is epi. The carrier universe `w` is
independent of `u`.
