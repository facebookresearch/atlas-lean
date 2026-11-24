# Finite Weyl word perm prod eq one

Caller-supplied finite Weyl words have trivial permutation product: if the
`toStableE` image of the head-left `List.ofFn`/`List.prod` ordered product of
the stable `StableSteinberg.weyl (a k) (b k) (hab k) (u k)` generators equals
`1`, then the ordered product of the corresponding `Equiv.swap`s at
`⟨a k, ha k⟩`, `⟨b k, hb k⟩` equals `1`. `[Field F]` is required by the
`bruhatMiddle` retraction in the proof; `ha hb` are the pointwise bounds into
`n` and `hab` is pointwise distinctness. Both sides use head-left `List.ofFn`
order, so the empty list (`m = 0`) gives `1 = 1`. Purpose: caller-supplied
permutation input for the finite-torus landing route. Nonclaims: no
finite-torus landing or containment, representation independence,
weight/diagonal conclusion, kernel generation, TWT claim, or Matsumoto theorem.
