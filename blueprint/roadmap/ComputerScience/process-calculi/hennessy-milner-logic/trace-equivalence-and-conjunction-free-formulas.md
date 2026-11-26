# Trace equivalence is equivalence on negation-free, conjunction-free formulas

Let $P$ be a set of processes and $(R_i)_{i \in I}$ a family of binary relations on $P$, the observation relations; $(p, p') \in R_i$ is an $i$-experiment on $p$. For a sequence $s = i_1 \dots i_n$ in $I^*$, an $s$-experiment on $p$ is a sequence $p = p_0, p_1, \dots, p_n$ with $(p_{k-1}, p_k) \in R_{i_k}$. Let $p \sim_e q$ if, for every $s \in I^*$, $p$ has an $s$-experiment if and only if $q$ has one. Then

$$p \sim_e q \iff p \sim_{\mathcal{N}} q,$$

where $\mathcal{N}$ is the fragment of [Hennessy–Milner logic](hennessy-milner-logic.md) with neither negation nor conjunction. No image-finiteness is needed.

## Depends on

- [Hennessy–Milner logic](hennessy-milner-logic.md)

## Sources

- M. Hennessy and R. Milner, "Algebraic laws for nondeterminism and concurrency", *Journal of the ACM* 32(1):137–161, 1985, <https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf>, Section 2.1 (the equivalence $\sim_e$ and $s$-experiments) and Section 2.2, Theorem 2.3.
