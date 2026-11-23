# Pivot columns of a reduced row echelon matrix

Let $R$ be a type with elements $0$ and
$1$, and let $A$ be a matrix over $R$ in reduced row echelon form whose rows are indexed by a
linearly ordered set and whose columns are indexed by a set with a relation $<$. Suppose that the
leading entry of row $i$ of $A$ is in column $c$, that is, $A_{ic} \neq 0$ and $A_{ij} = 0$ for
every column $j < c$. Then column $c$ of $A$ is the standard basis vector $e_i$: $A_{ic} = 1$ and
$A_{kc} = 0$ for every row $k \neq i$.
