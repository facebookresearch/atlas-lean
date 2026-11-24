# Horseshoe zero

The unop'd horseshoe maps compose to zero (unop of the op-side `zero`).
The `rfl`-equations unfold `horseshoeI`/`horseshoeP` (rather than `simp only`,
whose equation-lemma unfolding breaks `rw`-matching on these op-transported
terms).
