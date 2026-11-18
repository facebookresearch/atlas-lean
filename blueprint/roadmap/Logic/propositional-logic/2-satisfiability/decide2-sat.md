# SCC-based 2-SAT decision procedure

For a CNF formula $\varphi$, the procedure returns
false if $\varphi$ contains the empty clause; otherwise it returns true if and only if no block
of the strongly connected components computed for the implication graph of $\varphi$ contains a
literal together with its complementary literal.
