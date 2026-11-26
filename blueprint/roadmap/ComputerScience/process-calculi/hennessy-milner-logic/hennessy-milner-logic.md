# Hennessy–Milner logic

Let $P$ be a set of processes and $(R_i)_{i \in I}$ a family of binary relations on $P$, the observation relations; $(p, p') \in R_i$ is an $i$-experiment on $p$. The formulas of Hennessy–Milner logic form the least set $\mathcal{L}$ containing $\mathrm{T}$ and closed under conjunction $A \wedge B$, negation $\neg A$ and, for each $i \in I$, the modality $\langle i \rangle A$. Satisfaction $p \models A$ is defined by induction on formulas:

- $p \models \mathrm{T}$ for every $p \in P$;
- $p \models A \wedge B$ if $p \models A$ and $p \models B$;
- $p \models \neg A$ if not $p \models A$;
- $p \models \langle i \rangle A$ if $p' \models A$ for some $i$-experiment $(p, p')$.

$\mathrm{F}$ abbreviates $\neg \mathrm{T}$, $A \vee B$ abbreviates $\neg(\neg A \wedge \neg B)$, and $[i] A$ abbreviates $\neg \langle i \rangle \neg A$. Write $\mathcal{L}(p) = \{ A \in \mathcal{L} \mid p \models A \}$, and for a set $\mathcal{K} \subseteq \mathcal{L}$ write $p \sim_{\mathcal{K}} q$ if $p$ and $q$ satisfy the same formulas of $\mathcal{K}$. Two fragments matter: $\mathcal{M}$, the formulas without negation, and $\mathcal{N}$, the formulas of $\mathcal{M}$ without conjunction.

## Sources

- M. Hennessy and R. Milner, "Algebraic laws for nondeterminism and concurrency", *Journal of the ACM* 32(1):137–161, 1985, <https://www.scss.tcd.ie/matthew.hennessy/pubs/old/HMjacm85.pdf>, Section 2.2 ("Logical characterization"): the language $\mathcal{L}$, the satisfaction relation, the derived operators and the fragments $\mathcal{M}$ and $\mathcal{N}$.
