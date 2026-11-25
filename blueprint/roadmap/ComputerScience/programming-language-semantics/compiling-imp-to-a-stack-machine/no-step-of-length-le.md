# No step past the end of the program

Let $P$ be a program, that is a list of instructions,
and let $(pc, \sigma, s)$ be a configuration with $|P| \le pc$. Then the stack machine running $P$
has no step from $(pc, \sigma, s)$ to any configuration, since there is no instruction at
position $pc$ to fetch.

Hence the length of the code compiled from a command at base address $0$ is a halt address for
that code.
