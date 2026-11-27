# Structural properties of a typing judgment

For a typing judgment `HasType Γ t A` and
operations supplied by the language, namely `bind Γ x A` (the context `Γ` extended by a variable
`x` of type `A`), `inst e x v` (the term `e` with `x` instantiated by `v`), a context-extension
relation `Extends Γ Δ`, and the action `wk Γ Δ t` of weakening from `Γ` to `Δ` on terms: the
single-variable substitution lemma and weakening hold. A language whose contexts are finite maps
from names can take `wk` to be the identity; a de Bruijn language shifts variables.
