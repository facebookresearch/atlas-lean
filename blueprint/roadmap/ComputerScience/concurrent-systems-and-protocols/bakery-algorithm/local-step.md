# One atomic action of a bakery process

Let $s$ be a state of the bakery algorithm for $N$ processes and $p$ a process. The atomic actions of $p$ in $s$, each given by its new program counter and its new values of $\mathrm{choosing}[p]$ and $\mathrm{number}[p]$ (a value not mentioned is unchanged), are:

- **enter** (L1): from the noncritical section, set $\mathrm{choosing}[p] := 1$ and start reading the entries of all processes, $p$ included, with running maximum $0$;
- **read**: while reading with set $U$ of entries still to read and running maximum $m$, read $\mathrm{number}[k]$ for some $k \in U$, remove $k$ from $U$ and replace $m$ by $\max(m, \mathrm{number}[k])$;
- **end of reads**: when no entry is left to read, prepare to write with the running maximum $m$;
- **write**: about to write the running maximum $m$, set $\mathrm{number}[p] := 1 + m$ and move to the exit statement, where $\mathrm{choosing}[p]$ is about to be reset;
- **exit**: at the exit statement, set $\mathrm{choosing}[p] := 0$ and start the loop at L2 with index $0$;
- **L2**: at index $j < N$, proceed to L3 with index $j$ when $\mathrm{choosing}[j] = 0$;
- **L3**: at index $j < N$, proceed to L2 with index $j + 1$ unless $\mathrm{number}[j] \ne 0$ and $(\mathrm{number}[j], j) < (\mathrm{number}[p], p)$;
- **enter the critical section** from L2 with index $N$;
- **leave**: from the critical section, set $\mathrm{number}[p] := 0$ and return to the noncritical section;
- **fail**: in any state, return to the noncritical section with $\mathrm{choosing}[p] = \mathrm{number}[p] = 0$.

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: the program on p. 454 and the failure model ("We allow processor i to fail at any time, and then to be restarted in its noncritical section").
