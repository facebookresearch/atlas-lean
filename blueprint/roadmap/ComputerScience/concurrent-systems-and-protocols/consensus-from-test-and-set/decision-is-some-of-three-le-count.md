# Wait-free termination of test-and-set consensus

In the two-process test-and-set consensus protocol, process $i$ first writes its input to its own register, and in its next step applies test-and-set to a shared bit, setting it and returning its old value in one atomic step. If the old value was false, the process has won but has not yet decided: it decides its own input in its following step. Otherwise its following step reads the other process's register and decides the value found there. In every execution from the initial state, in which no register is written, the bit is false and no process has decided, a process that has taken at least three steps has decided, whatever the other process does.

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13 (1991), 124-149.
