# Improving Move of step ne

For any weights `T` (no symmetry is needed), thresholds `U`, neuron `i` and state `v`: if the
update of neuron `i` changes the state (`step T U i v ≠ v`), then it is an improving move that
strictly lowers neuron `i`'s cost `cost T U i`.
