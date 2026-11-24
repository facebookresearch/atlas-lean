# Databases conforming to a schema

Let $N$ be a set of relation names. A database
schema assigns to each name $n \in N$ a finite set of attributes $\mathrm{sch}(n)$, and a
database assigns to each name $n$ a finite set of tuples $\mathrm{db}(n)$. The database
$\mathrm{db}$ conforms to the database schema $\mathrm{sch}$ when, for every name $n$, the
set $\mathrm{db}(n)$ is a relation over $\mathrm{sch}(n)$.
