# The Needleman–Wunsch recurrence

For all letters $a, b$ and sequences $x, y$,

$$\mathrm{NW}(a x, b y) = \max\bigl(\mathrm{NW}(x, y) + \sigma(a, b),\ \mathrm{NW}(x, b y) + g,\ \mathrm{NW}(a x, y) + g\bigr),$$

where $\mathrm{NW}$ is the [Needleman–Wunsch score](nw-score.md).
