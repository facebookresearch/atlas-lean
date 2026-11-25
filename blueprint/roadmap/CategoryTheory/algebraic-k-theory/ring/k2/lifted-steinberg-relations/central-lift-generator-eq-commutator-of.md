# Central Lift Generator eq commutator of aux

Auxiliary-index independence for the canonical central lift.

For a central extension `S : GroupExtension N E (StableE R)` over an arbitrary
ring `R`, the canonical generator `centralLiftGenerator S ⟨i, j, hij, a⟩`
(defined via the fresh index `max i j + 1`) coincides with `⁅u, v⁆` for *any*
auxiliary index `k` distinct from `i` and `j` and any lifts `u, v : E` with
`S.rightHom u = StableE.natElementary i k _ a` and
`S.rightHom v = StableE.natElementary k j _ 1`. The proof uses only centrality
of `S` and the Hall–Witt identity (via exact distant-commutation), not a
chosen set-theoretic splitting of `S`.
