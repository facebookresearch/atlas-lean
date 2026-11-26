# A uniform tape of length n + 1 splits into head and tail

For a finite nonempty type `α` and `g : (Fin (n + 1) → α) → PMF γ`, sampling a
tape uniformly from `Fin (n + 1) → α` and applying `g` equals sampling a head
`a` uniformly from `α`, a tail `ρ` uniformly from `Fin n → α`, and applying
`g` to `Fin.cons a ρ`.
