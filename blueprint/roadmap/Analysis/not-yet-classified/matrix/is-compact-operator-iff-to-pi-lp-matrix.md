# Compactness detected by finite rectangular entries

Let `R` be a semiring and `E,F`
additive commutative groups with topologies and `R`-module structures. Let `m,n` be index
types; the carriers `PiLp 2 (fun _ : n => E)` and `PiLp 2 (fun _ : m => F)` have their
product topologies. assume `m,n` are finite, equality on `n` is decidable, and addition on
`F` is continuous. An operator `T : PiLp(E^n) →L[R] PiLp(F^m)` is compact exactly when
every recovered matrix entry `T.toPiLpMatrix i j` is compact.
