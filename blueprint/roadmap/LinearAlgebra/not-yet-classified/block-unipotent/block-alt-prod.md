# Block Alt Prod

Alternating product of block unipotents in `GL (α ⊕ β) R`.

Orientation: `Sum.inl A` uses `upperUnit` as `[[1, A],[0,1]]` and
`Sum.inr C` uses `lowerUnit` as `[[1,0],[C,1]]`. Multiplication order is
`List.prod` of the `Sum.elim`-image, so the head factor multiplies on the
left: `blockAltProd (a :: L) = (Sum.elim upperUnit lowerUnit a) *
blockAltProd L`. Works over any `[Ring R]` with `[Fintype α] [Fintype β]`;
empty list is `1` and zero-dimensional `α` or `β` yields trivial blocks
definitionally. This is a pure matrix recurrence; no elementary-subgroup,
kernel, pivot, alternation, or C3 claim is made.
