# Asymptotic security

**Asymptotic security** against a class of adversary families: every admissible family `A`
(one adversary `A n` per security parameter `n`) has negligible advantage `adv n (A n)`
(Katz and Lindell, the shape of Definitions 3.8, 3.22, 4.2, 11.2, 12.2). The class
`Admissible` is a parameter; see `PolyQueryBounded`. The statement is vacuous when no family is
admissible, in particular when some `Adv n` is empty (for example, adversaries whose coin type or
message type is empty); the instances below rule that out by requiring nonempty message and coin
types (see `exists_polyQueryBounded_cpa` and its siblings).
