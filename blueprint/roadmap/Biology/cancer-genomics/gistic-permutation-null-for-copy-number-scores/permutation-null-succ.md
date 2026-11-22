# Convolution step

For sample values $x_1, \dots, x_{S+1}$ on $M$ markers, every marker $m$ and every real $g$,

$$P_{S+1}(g) = \sum_{v=1}^{M} \frac{1}{M}\, P_S\bigl(g - x_{S+1}(v)\bigr),$$

where $P_{S+1}$ is the [permutation null](permutation-null.md) at $m$ of all $S + 1$ samples and $P_S$ that of the first $S$: adding a sample convolves the null with its empirical law over markers.
