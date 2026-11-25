# Collision resistance

**Collision resistance** of a family of keyed hash functions (Katz and Lindell,
Definition 5.2): every admissible family of collision finders has negligible advantage. A finder
makes no oracle queries, so the admissible class is an argument (eventually: probabilistic
polynomial time); with the class of all families this is security against unbounded finders. The
input and coin types must be nonempty, or there would be no finder and the notion would hold
vacuously (`CollisionFinder.nonempty`); whether some family is admissible depends on
`Admissible`. No efficiency or compression condition is imposed on `H`, so an injective family is
collision resistant (see the module documentation).
