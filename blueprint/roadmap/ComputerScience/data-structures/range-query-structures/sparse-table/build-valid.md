# Built sparse tables are valid

For every list $a$ over a type with a minimum operation,
the sparse table built from $a$ is valid: its stored rows are exactly the levels
$0, 1, \dots, \lfloor \log_2 n \rfloor$ of $a$, in this order, where $n$ is the length of $a$
and $\lfloor \log_2 0 \rfloor$ is taken to be $0$.
