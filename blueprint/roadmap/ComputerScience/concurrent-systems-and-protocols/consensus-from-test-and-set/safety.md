# Safety of test-and-set consensus

In the two-process test-and-set consensus protocol, process $i$ first writes its input to its own register, and in its next step applies test-and-set to a shared bit, setting it and returning its old value in one atomic step. If the old value was false, the process has won but has not yet decided: it decides its own input in its following step. Otherwise its following step reads the other process's register and decides the value found there. In every reachable state, any two decisions agree, and every decision is the input of one of the two processes.

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13 (1991), 124-149.
