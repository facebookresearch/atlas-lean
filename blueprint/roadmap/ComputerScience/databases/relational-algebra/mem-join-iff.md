# Membership in a join

Let $r$ be a relation over the schema $S$ and $s$ a relation over
the schema $S'$, that is, finite sets of tuples each over $S$, respectively each over $S'$. A
tuple $t$ belongs to the natural join $r \bowtie s$ if and only if $t$ is over $S \cup S'$, the
restriction of $t$ to $S$ belongs to $r$, and the restriction of $t$ to $S'$ belongs to $s$.
