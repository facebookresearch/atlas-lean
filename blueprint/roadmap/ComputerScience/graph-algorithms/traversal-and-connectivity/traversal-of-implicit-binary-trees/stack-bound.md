# Depth budget bounds the depth-first stack size

The depth budget bounds the stack by `D + 1` at every round; each pending state
satisfies the resource invariant. This is a list-size bound, not a machine-space model.
