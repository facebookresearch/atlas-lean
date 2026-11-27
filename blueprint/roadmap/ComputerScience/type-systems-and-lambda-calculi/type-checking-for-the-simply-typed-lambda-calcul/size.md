# Size of a raw term

Writing $|t|$ for the size of a raw term $t$, the size counts the
syntax nodes of $t$: a variable has size $1$, an application $f\,a$ has size $|f| + |a| + 1$,
and a lambda abstraction $\lambda A.\,t$ has size $|t| + 1$, so the type annotation $A$ is
not counted.
