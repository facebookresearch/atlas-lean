# Parent configuration counts sum over family configurations

Let $V$ be a set of variables with finite value sets, $D$ a finite list of cases and
$P \subseteq F$ finite sets of variables. For every configuration $j$ of $P$, the number of cases
matching $j$ is the sum of the counts of the configurations of $F$ that restrict to $j$:
$N_P(j) = \sum_{c \mapsto j} N_F(c)$.
