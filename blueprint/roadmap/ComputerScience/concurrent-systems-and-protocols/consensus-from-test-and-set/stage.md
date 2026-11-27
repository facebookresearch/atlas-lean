# Stages of a process in test-and-set consensus

In the two-process test-and-set consensus protocol, each process is at one of five stages: about to write its input to its own register; about to apply test-and-set to the shared bit; having won the test-and-set and about to decide its own input; having lost it and about to read the other process's register and decide the value found there; or decided.
