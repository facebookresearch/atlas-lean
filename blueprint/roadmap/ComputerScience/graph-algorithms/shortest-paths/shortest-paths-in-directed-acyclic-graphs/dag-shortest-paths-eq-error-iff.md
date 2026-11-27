# Failure output of DAG shortest paths

For a list $E$ of integer-weighted edges on $n$
vertices, a source $s$, and lists $P$ and $R$ of vertices, the DAG shortest-path algorithm on $E$
from $s$ returns the error $(P, R)$ if and only if Kahn's topological sort of the directed graph
obtained from $E$ by forgetting weights fails after processing $P$ and leaving $R$.
