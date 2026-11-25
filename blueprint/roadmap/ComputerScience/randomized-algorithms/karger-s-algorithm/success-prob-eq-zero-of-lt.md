# Every run returns at least the minimum cut size

If every cut of a valid state with at
least two vertices has size at least `k`, the contraction process returns a value `j < k` with
probability `0`, at any fuel value including early fuel exhaustion. So the minimum over several
runs is the minimum cut size exactly when some run returns it.
