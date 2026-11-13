# The oral messages algorithm solves the Byzantine generals problem

Let $G$ be a finite set
of more than $3m$ generals, at most $m$ of whom are traitors, and let the commander $c \in G$ run
$\mathrm{OM}(m)$ with the value $v$, with no superiors and with all the other generals as
lieutenants. Then, whatever the traitors send, any two loyal lieutenants decide the same value,
and if $c$ is loyal, every loyal lieutenant decides $v$.

This is Theorem 1 of Lamport–Shostak–Pease, applied to all the generals.
