# Global state of test-and-set consensus

A global state of the two-process test-and-set consensus protocol, with decision values in a type $V$, consists of the stage of each process, the content of each process's single-writer register (empty until written, then a value in $V$), the shared test-and-set bit, the winner (the process whose test-and-set returned false, if any; this component is recorded by the steps but never read by them), and the decision of each process (none until it decides, then a value in $V$).
