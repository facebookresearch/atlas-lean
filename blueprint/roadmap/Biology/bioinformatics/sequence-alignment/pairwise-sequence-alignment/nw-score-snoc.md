# The Needleman–Wunsch recurrence, end-peeling

For all sequences $x, y$ and letters $a, b$,

$$\mathrm{NW}(x a, y b) = \max\bigl(\mathrm{NW}(x, y) + \sigma(a, b),\ \mathrm{NW}(x, y b) + g,\ \mathrm{NW}(x a, y) + g\bigr),$$

where $\mathrm{NW}$ is the [Needleman–Wunsch score](nw-score.md).
