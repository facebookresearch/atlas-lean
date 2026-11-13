# Join of the projections of a relation

For a relation $r$ (a finite set of tuples) and a
list of schemes $S_1, \dots, S_n$, this is the natural join of the projections
$\pi_{S_1} r, \dots, \pi_{S_n} r$, computed as
$\pi_{S_1} r \bowtie (\pi_{S_2} r \bowtie (\cdots \bowtie (\pi_{S_n} r \bowtie U)))$, where $U$ is
the relation containing only the empty tuple; for the empty list it is $U$.
