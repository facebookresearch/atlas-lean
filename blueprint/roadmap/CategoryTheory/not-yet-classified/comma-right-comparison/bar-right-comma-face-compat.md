# Bar Right Comma face compat

Full face compatibility for the right-comma `Data` isomorphism.

Dispatches an arbitrary `i : Fin (n + 2)` by `i.val = 0`, `i.val = n + 1`,
and the interior `q := ⟨i.val - 1, by omega⟩`.
