# Top-level cut elimination

**Top-level cut elimination** (Wadler, Theorem 2): if `P ⊢ Γ`, then
`P ⟹* Q` for some `Q` that is not a cut. The cut propositions are
unrestricted. Not being a cut constrains only the outermost constructor:
`Q` may still contain cuts guarded by a prefix.
