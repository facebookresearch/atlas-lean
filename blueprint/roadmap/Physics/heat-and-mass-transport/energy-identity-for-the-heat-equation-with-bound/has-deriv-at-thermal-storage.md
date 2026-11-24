# With symmetric conductances the stored heat changes at the input rate

Let `ι` be a finite index set of nodes, with capacities `C i`, conductances `G i j` such that
`G i j = G j i`, temperatures `T i` differentiable at time `t` with derivatives `dT i` and inputs
`Q i`, such that every node obeys `C i dT i = ∑_j G i j (T j(t) - T i(t)) + Q i`. Then the stored
heat `∑_i C i T i` has at `t` the derivative `∑_i Q i`: conduction between nodes cancels.
Equivalently, in zone form with boundary inputs `b i` and heating powers `P i` (take
`Q i = b i(t) + P i(t)`): if every `T i` has derivative `v i(t)` at `t` and
`C i v i(t) = ∑_j G i j (T j(t) - T i(t)) + b i(t) + P i(t)`, the total heat inventory `∑_i C i T i`
has derivative `∑_i (b i(t) + P i(t))` at `t`. Only data at the time `t` is used, and no sign
condition on the capacities or conductances is needed.
