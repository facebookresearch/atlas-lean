# The data-free one-place buffer

The process $\mathit{buf}$ is the one-place buffer in its
empty state. By the specification it accepts on $\mathit{acc}$ and becomes full, and the full
buffer delivers on $\mathit{del}$ and becomes empty again, so
$\mathit{buf} = \mathit{acc}.\overline{\mathit{del}}.\mathit{buf}$.
