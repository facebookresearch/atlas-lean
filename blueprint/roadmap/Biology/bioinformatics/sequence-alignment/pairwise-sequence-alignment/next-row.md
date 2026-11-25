# Next row of the Needleman–Wunsch table

For a letter $a$, a sequence $y$ and a previous row $r = (r_0, r_1, \dots)$, the next row is $r_0 + g$ followed by the [remaining cells](next-row-aux.md) for $a$, $y$, $(r_1, r_2, \dots)$, upper-left value $r_0$ and left value $r_0 + g$, where $r_0$ is taken to be $0$ if $r$ is empty.
