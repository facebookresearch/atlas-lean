# Stopping rule of the threshold algorithm

For a run of the threshold algorithm with
buffers $B_0, B_1, \ldots$ and a position $p$, the stopping rule holds after round $p + 1$ when
the buffer $B_{p+1}$ holds at least $k$ objects whose aggregate grade is at least the threshold
$\tau = t(\underline{x}_1, \ldots, \underline{x}_m)$, where $\underline{x}_i$ is the grade at
position $p$ of list $i$. Fagin, Lotem and Naor state the rule for all objects seen: at least $k$
of the objects seen in the first $p + 1$ rounds have aggregate grade at least $\tau$. Since the
buffer $B_{p+1}$ is a top-$k$ choice among those objects, the two forms hold for the same rounds;
with the buffered form, every decision of the algorithm depends only on its buffer and the round.
The algorithm halts at the first round at which the stopping rule holds and returns its buffer;
the rule may go on holding after that round.
