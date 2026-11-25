# Nerve Opp Data

Opposite nerve data.

Objects are `ComposableArrows (SingleObj Gᵐᵒᵖ) n`; faces and degeneracies are
the pinned nerve maps. Each identity is nerve functoriality (`map_comp`,
`map_id`) plus the corresponding pinned `SimplexCategory` relation, folded
across the opposite via `op_comp`; no bare `rfl` is used.
