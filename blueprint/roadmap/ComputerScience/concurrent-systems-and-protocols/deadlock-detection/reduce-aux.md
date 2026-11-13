# The detection algorithm with fuel

Given the fuel, a number of steps, together with the free
resource vector $w$ and a list of pending processes, the algorithm returns two lists: the processes
that finished, in order, and the processes left over. With fuel $0$, or when no pending process has
a request at most $w$, no process finishes and all the pending processes are left over. Otherwise
the fuel is $n + 1$ for some $n$; take the first pending process $p$ whose request is at most $w$
and run the algorithm with fuel $n$, free vector $w$ plus the allocation of $p$, and the list with
that entry of $p$ removed. The result is $p$ followed by the processes that finished there,
together with the processes left over there.
