# Generator of Kingman's block-counting process

For a natural number $n$, the $(n+1) \times (n+1)$ real matrix $G_n$, with rows and columns indexed by $\{0, \dots, n\}$, whose entry in row $k$ and column $j$ is

- $\binom{k}{2}$ if $j = k - 1$,
- $-\binom{k}{2}$ if $j = k$,
- $0$ otherwise.

It is the rate matrix of Kingman's block-counting process, the pure-death process on $\{0, \dots, n\}$ in which $k$ lineages become $k - 1$ at rate $\binom{k}{2}$, with time measured in units of $M = 2N$ generations.
