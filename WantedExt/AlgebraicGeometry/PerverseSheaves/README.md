# Rational perverse sheaves

- `Basic.lean` defines complex varieties, algebraic constructibility,
  support/cosupport conditions, and the public `PerverseSheafTheory` interface.
  Given that interface, `PerverseSheaf` is its heart and `perverseCohomology`
  is computed by t-structure truncations.
- `PerverseSheavesWanted.lean` requests the middle perverse theory, its heart,
  and the abelian-category structure for general complex varieties.
- `../DeCataldoMiglioriniDecompositionWanted.lean` uses that interface for
  projective decomposition and semisimplicity.

The sheaves are rational Betti sheaves on the ordinary analytic topology of
`X(ℂ)`. The imported `ComplexAnalytification` constructs this topological
space and algebraic-map continuity. This is the topology used by local
systems, stalks, costalks, and the Hodge theoretic decomposition theorem.

Batteries wanted markers in this pin are private to their declaring file.
Consumers therefore use the public target interface
`[PerverseSheafTheory X]`; they do not repeat the construction request.

References: de Cataldo–Migliorini, *The Hodge theory of algebraic maps*,
§§3.3, 3.6, 3.8 ([source](https://arxiv.org/abs/math/0306030)); their survey,
§2.3 ([source](https://arxiv.org/abs/0712.0349)).
