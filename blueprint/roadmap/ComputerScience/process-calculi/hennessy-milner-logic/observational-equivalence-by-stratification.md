# Observational equivalence by stratification

Let $P$ be a set of processes and $(R_i)_{i \in I}$ a family of binary relations on $P$, the observation relations; $(p, p') \in R_i$ is an $i$-experiment on $p$. Define relations $\sim_n$ on $P$ by $\sim_0 = P \times P$ and $p \sim_{n+1} q$ if for every $i \in I$:

1. $(p, p') \in R_i$ implies $(q, q') \in R_i$ and $p' \sim_n q'$ for some $q'$;
2. $(q, q') \in R_i$ implies $(p, p') \in R_i$ and $p' \sim_n q'$ for some $p'$.

Processes $p$ and $q$ are *observationally equivalent*, $p \sim q$, if $p \sim_n q$ for every $n$. Equivalently $\sim = \bigcap_n E^n(P \times P)$, where for $S \subseteq P \times P$ the relation $E(S)$ holds of $(p, q)$ when the two clauses above hold with $S$ in place of $\sim_n$. A relation $R_i$ is *image-finite* if $\{ p' \mid (p, p') \in R_i \}$ is finite for every $p$.

## Sources

- M. Hennessy and R. Milner, "Algebraic laws for nondeterminism and concurrency", *Journal of the ACM* 32(1):137–161, 1985, <https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf>, Section 2.1: the relations $\sim_n$, the map $E$ and the definition of image-finiteness.
