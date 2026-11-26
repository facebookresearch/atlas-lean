# The output heading is the vertex set

If a relational expression $Q$ yields a [join hypergraph](join-hypergraph-2.md) $H$ for a database schema, then schema inference on $Q$ with the same schema returns the vertex set of $H$. Thus every output column of the join is a vertex and every vertex is an output column, even if the ambient attribute type also contains other names.
