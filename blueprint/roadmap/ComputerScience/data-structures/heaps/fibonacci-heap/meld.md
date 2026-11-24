# Melding Fibonacci heaps

The meld of Fibonacci heaps $H_1$ and $H_2$ is the Fibonacci heap
whose root list is the root list of $H_1$ followed by that of $H_2$, and whose cached minimum is
the smaller of the two cached minima when both heaps have one, and otherwise the cached minimum
of whichever heap has one (none if neither does).

No linking happens until the next minimum deletion.
