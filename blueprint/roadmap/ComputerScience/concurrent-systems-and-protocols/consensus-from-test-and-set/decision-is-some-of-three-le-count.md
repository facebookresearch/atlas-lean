# Wait-free termination of test-and-set consensus

In the two-process test-and-set consensus protocol, process $i$ writes its input to its own register, then applies test-and-set to a shared bit (setting it and returning its old value in one atomic step); if the old value was false it decides its own input, and otherwise it reads the other process's register and decides the value found there. In every execution, a process that has taken at least three steps has decided, whatever the other process does.

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13 (1991), 124-149.
