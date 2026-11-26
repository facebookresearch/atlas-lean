# Finite Family

A finite family of objects of `C`, indexed by a bundled finite type.

We keep the index in `FintypeCat.{0}` (small) and not in a larger universe;
consequently `FiniteFamily C` lives in `Type (max u₁ 1)` when `C : Type u₁`,
i.e. there is a universe bump of at most one due to the `FintypeCat` bundle.
