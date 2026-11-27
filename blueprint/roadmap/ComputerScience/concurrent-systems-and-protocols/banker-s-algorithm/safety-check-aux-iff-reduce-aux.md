# The safety loop agrees with deadlock detection

Run deadlock detection on the state in which each process holds its allocation and requests its remaining need (claim minus allocation). For the same fuel, initial work vector and list of pending processes, the banker's safety loop succeeds exactly when the detection loop leaves no process pending. Both loops repeatedly pick the first pending process whose need is at most the current work, add its allocation to the work and remove it. No duplicate-free assumption is needed for the loops.
