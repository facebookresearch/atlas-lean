# Stabilization elementary eq commutator

Successor stabilization as a commutator through the new last coordinate.

For `i j : Fin k`, `stabilization (elementary i j a)` equals the commutator
`⁅E_{i', last}(a), E_{last, j'}(1)⁆`, where `i' = finSumFinEquiv (Sum.inl i)`,
`j' = finSumFinEquiv (Sum.inl j)`, `last = finSumFinEquiv (Sum.inr 0)`.
This exhibits every stabilized elementary generator as a single commutator,
with second coefficient `1`, directly usable for `E_∞ ≤ [GL_∞, GL_∞]`.
