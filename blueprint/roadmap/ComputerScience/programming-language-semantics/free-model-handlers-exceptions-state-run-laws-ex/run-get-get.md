# Reading the state twice

For a continuation `k`, reading the state twice and passing both values to `k`
behaves as reading once and passing the value twice: the get-get equation of
Plotkin and Power. The equation holds after running the computation with `run`
from any initial state `s0`; it is not an equality of the unevaluated
computations.
