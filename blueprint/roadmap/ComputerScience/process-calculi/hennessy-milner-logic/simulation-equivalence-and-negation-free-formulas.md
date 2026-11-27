# Simulation equivalence is equivalence on negation-free formulas

Let $P$ be a set of processes and $(R_i)_{i \in I}$ a family of binary relations on $P$, the observation relations; $(p, p') \in R_i$ is an $i$-experiment on $p$. Define $\sqsubseteq_0 = P \times P$ and $p \sqsubseteq_{n+1} q$ if for every $i \in I$, $(p, p') \in R_i$ implies $(q, q') \in R_i$ and $p' \sqsubseteq_n q'$ for some $q'$; let $p \sqsubseteq q$ if $p \sqsubseteq_n q$ for every $n$, and $p \simeq q$ if $p \sqsubseteq q$ and $q \sqsubseteq p$. If every $R_i$ is image-finite, then

$$p \simeq q \iff p \sim_{\mathcal{M}} q,$$

where $\mathcal{M}$ is the fragment of [Hennessy–Milner logic](hennessy-milner-logic.md) without negation. In general $\simeq$ is strictly coarser than [observational equivalence](observational-equivalence-by-stratification.md).

## Depends on

- [Hennessy–Milner logic](hennessy-milner-logic.md)
- [Observational equivalence by stratification](observational-equivalence-by-stratification.md)

## Sources

- M. Hennessy and R. Milner, "Algebraic laws for nondeterminism and concurrency", *Journal of the ACM* 32(1):137–161, 1985, <https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf>, Section 2.2: the asymmetric map $AE$, the relations $\sqsubseteq_n$, $\sqsubseteq$ and $\simeq$, and Theorem 2.4; the example showing that $\simeq$ is weaker than $\sim$ is in Section 3.2.
