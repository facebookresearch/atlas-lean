# Two-process consensus protocol from test-and-set

In the two-process test-and-set consensus protocol, process $i$ writes its input to its own register, then applies test-and-set to a shared bit (setting it and returning its old value in one atomic step); if the old value was false it decides its own input, and otherwise it reads the other process's register and decides the value found there. Each write, test-and-set and read-and-decide is one atomic step of the process taking it, and the processes may interleave arbitrarily.

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13 (1991), 124-149.
