# Signed incidence matrix of an arc network

Let $V$ and $E$ be finite sets and let each arc $e \in E$ run from its tail $t(e) \in V$ to its head $h(e) \in V$; parallel arcs and loops are allowed. The signed incidence matrix of the network is the real $V \times E$ matrix

$$B_{ve} = [h(e) = v] - [t(e) = v],$$

where $[P]$ is $1$ if $P$ holds and $0$ otherwise. The column of an arc with distinct endpoints is $+1$ at its head and $-1$ at its tail, the column of a loop is zero, and parallel arcs give separate columns.
