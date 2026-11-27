# Find paths are short under union by rank

In a union-find structure built by make-set,
find and union, every find path has at most $\lfloor \log_2 n \rfloor$ edges, $n$ being the
number of nodes (an index that is not a node has a find path with no edges, and
$\lfloor \log_2 0 \rfloor$ is read as $0$).
