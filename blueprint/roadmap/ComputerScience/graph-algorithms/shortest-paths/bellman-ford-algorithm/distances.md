# Bellman-Ford distance table

For a graph on the vertices $0, \dots, n-1$, the output of a
successful Bellman-Ford run consists of a source vertex $s$, for every vertex a distance that is
either an integer or $\infty$, and for every vertex an optional predecessor edge (a weighted
directed edge, or none).

The structure only records these values; that they are shortest-path data is proved separately.
