# Lamport signatures are correct

For a finite nonempty `X`, a type `Y` with decidable equality and every function `f : X → Y`, the Lamport one-time signature scheme `lamport
f` is correct: every honestly generated signature verifies under the matching
public key.
