# Flatten ATo Flatten BHom

Identity-component hom from flattened A to flattened B.

Mapping of flattened indices:
- `A(none, unit)` ↦ `B(none, none)` both `O(outer)`
- `A(some i, none)` ↦ `B(none, some i)` both `O(middle i)`
- `A(some i, some j)` ↦ `B(some ⟨i, j⟩, unit)` both `O(inner ⟨i,j⟩)`

Inverse splits accordingly, with identity component morphisms.
