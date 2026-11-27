# Every run returns at least the minimum cut size

If every cut of a valid state with at least two vertices has size at least $k$, the contraction process returns a value $j < k$ with probability $0$, at any fuel value including early fuel exhaustion. In particular this holds when $k$ is the minimum cut size of the state, and conversely a valid state with at least two vertices has a cut, so its minimum cut size is at least any such $k$. So the minimum over several runs is the minimum cut size exactly when some run returns it.
