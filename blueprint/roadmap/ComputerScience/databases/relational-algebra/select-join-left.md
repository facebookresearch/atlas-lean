# Selection pushdown into the left operand of a join

Let $r$ be a relation over a schema
$S$, that is, a finite set of tuples each defined exactly on the attributes of $S$, and let $s$ be
any finite set of tuples. If every attribute of the selection condition $c$ lies in $S$, then
$\sigma_c(r \bowtie s) = \sigma_c(r) \bowtie s$, where $\sigma_c$ is selection by $c$ and
$\bowtie$ is the natural join.
