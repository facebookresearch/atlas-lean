# Typing is sound

Let $\mathrm{sch}$ be a database schema, assigning a finite set of attributes to each relation
name, and let $\mathrm{db}$ be a database that conforms to $\mathrm{sch}$ (each $\mathrm{db}(n)$ is
a relation over $\mathrm{sch}(n)$). For every relational algebra query $e$ whose schema with
respect to $\mathrm{sch}$ is defined and equal to $S$, the value of $e$ on $\mathrm{db}$ is a
relation over $S$: every tuple in it is defined exactly on the attributes of $S$.
