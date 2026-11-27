# A process's final vector is zero or one of its timestamps

Run the vector clock
algorithm over an execution, starting from all vectors $0$. For every process $p$, the vector
held by $p$ at the end is either the zero vector or the vector timestamp of some event of $p$
in the execution.
