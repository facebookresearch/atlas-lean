# Successful output of DAG shortest paths

For a list $E$ of integer-weighted edges on $n$
vertices, a source $s$, and a distance record $D$, the DAG shortest-path algorithm on $E$ from $s$
returns $D$ if and only if there is a topological order $\sigma$ of the directed graph obtained
from $E$ by forgetting weights such that Kahn's topological sort of that graph succeeds with
$\sigma$ and $D$ is the result of the one-pass relaxation from $s$ in the order $\sigma$.
