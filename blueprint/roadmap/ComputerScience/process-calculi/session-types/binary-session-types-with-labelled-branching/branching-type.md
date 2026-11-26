# Finite branching session types

Finite branching type: `send`/`recv` one sort (Def 5.1 output/input),
`select` internal choice, `branch` external choice, `end` inaction `1`.
Excludes recursion, the type `⊥`, delegation and tuple payloads. Equality is
syntactic; compare choices with `PermEquiv`.
