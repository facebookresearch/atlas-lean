# Nonce Close

The hiding hypothesis on `H`: for every message, the digest of a uniform nonce and that
message is `ε`-close to uniform on `D`. The key `s` is fixed and only the nonce is random, so this
is an assumption on the fixed function `H s`, not a consequence of collision resistance or of
random-oracle hiding (Katz and Lindell, Section 5.6.5). For example, with a one-element nonce
space and `D = Bool` every nonce digest is a point mass, at statistical distance `1 / 2` from
uniform, for every choice of `H s`.
