# Nerve Data

Nerve simplicial data.

Objects are `ComposableArrows C n`; faces and degeneracies are the nerve maps.
Each identity is nerve functoriality (`map_comp`, `map_id`) plus the
corresponding `SimplexCategory` relation, folded across the opposite via
`op_comp`.
