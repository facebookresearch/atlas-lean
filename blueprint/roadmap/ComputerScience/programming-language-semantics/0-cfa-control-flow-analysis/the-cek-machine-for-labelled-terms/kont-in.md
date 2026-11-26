# Continuations from a program

`KontIn P k` says that every frame of `k` belongs to an
application of `P`: an `ar` frame holds the argument of an application of `P` with the frame's
label and an environment from `P`, and an `fn` frame holds the label of an application of `P` and
a closure from `P`.
