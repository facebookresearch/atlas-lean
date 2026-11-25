# Verification conditions give a diagram derivation

For an annotated IMP command `c` and assertions `P` and `Q`, if `P` entails
the computed precondition of `c` for `Q` and the verification conditions of
`c` for `Q` hold, then the compiled diagram of `c` has a traced Hoare
derivation from the `P`-states to the `Q`-states.
