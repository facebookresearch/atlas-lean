# Stopping rule of the threshold algorithm

For a run of the threshold algorithm with
buffers $B_0, B_1, \ldots$ and a position $p$, the stopping rule holds after round $p + 1$ when
the buffer $B_{p+1}$ holds at least $k$ objects whose aggregate grade is at least the threshold
$t(\underline{x}_1, \ldots, \underline{x}_m)$, where $\underline{x}_i$ is the grade at position
$p$ of list $i$. The algorithm halts at the first round at which the stopping rule holds and
returns its buffer.
