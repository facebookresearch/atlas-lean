# The adjacent descent positions

Let `n : ℕ` and `σ : Equiv.Perm (Fin n)`. `descentPositions σ` is the finite set of `j : Fin
n` such that `j.val+1<n` and `σ j > σ(j+1)`. The successor bound omits the final position.
