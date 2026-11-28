# Regular resolution effectively simulates resolution

Regular resolution, which never resolves on a variable twice along a path, is exponentially weaker than resolution under ordinary simulation, but the two are equivalent under effective simulation: renaming each variable into a chain of equivalent copies turns any resolution refutation into a polynomial-size regular refutation of the padded formula.

**Effective simulation** (the notion of Pitassi and Santhanam). Let $P$ and $Q$ be proof systems for a class $\mathcal C$ of propositional formulas, where a proof means a refutation of satisfiability and the size $|\Gamma|$ of a formula is its number of symbols. $P$ *effectively simulates* $Q$ if there is a function $f:\mathcal C\times\mathbb N\to\mathcal C$ such that $f(\Gamma,s)$ is computable in time polynomial in $|\Gamma|+s$ and is satisfiable if and only if $\Gamma$ is, and such that whenever $s$ is at least the size of the smallest $Q$-proof of $\Gamma$, the formula $f(\Gamma,s)$ has a $P$-proof of size polynomial in $|\Gamma|+s$. A resolution derivation is a sequence of distinct clauses, each in $\Gamma$ or a resolvent of two earlier ones, viewed as a DAG; its size is the number of clauses, its height is the number of edges on a longest path, and it is *regular* if no variable is resolved on more than once along any directed path.

**Theorem.** Regular resolution effectively simulates resolution. Concretely, for a CNF $\Gamma$ with $n$ variables and an integer $h\ge1$, let $W[x,j]$ for $x\in\mathrm{var}(\Gamma)$ and $j\in[h-1]$ be new variables, identify $W[x,h]$ with $x$, and set

$$
f(\Gamma,h)=\Gamma\wedge\bigwedge_{x\in\mathrm{var}(\Gamma)}\ \bigwedge_{j\in[h-1]}\bigl(\neg W[x,j]\vee W[x,j+1]\bigr)\wedge\bigl(W[x,j]\vee\neg W[x,j+1]\bigr).
$$

Then $f(\Gamma,h)$ is satisfiable if and only if $\Gamma$ is, and if $\Gamma$ has a resolution refutation of size $s$ and height $h$, then $f(\Gamma,h)$ has a regular resolution refutation of size at most $6hns$ and height at most $hn$. Since a refutation of size $s$ has height less than $s$, the formula $f(\Gamma,s)$ has a regular refutation of size polynomial in $|\Gamma|+s$ whenever $s$ is at least the size of the smallest resolution refutation of $\Gamma$.

## Expansion

The added 2-clauses say $W[x,j]\leftrightarrow W[x,j+1]$, so the $W[x,j]$ are new names for $x$. Given a refutation $\Pi$ of $\Gamma$, the *irregularity height* $L_D(x)$ of $x$ at a clause $D$ is the largest number of resolution steps on $x$ along a path from $D$ to the empty clause, and $D$ is replaced by $g(D)=\bigvee_{p\in D}W[p,L_D(p)]$. A clause with higher levels can be *lowered* to one with lower levels by resolving with the equivalence clauses one level at a time. For an initial clause $C$ the regular refutation lowers $C$ to $g(C)$; for a resolution of $A$ and $B$ on $y$ into $C$, it lowers $g(A)$ and $g(B)$ so that every literal of $C$ sits at its level $L_C$ and $y$ sits one level higher, and resolves on $W[y,L_C(y)+1]$ to get $g(C)$. Levels strictly decrease along every path for each $x$, so no $W[x,j]$ is resolved on twice, and the empty clause is $g(\bot)$. The counting $s+2hn+(2hn+1)s\le6hns$ gives the size; height at most $hn$ holds because a regular refutation over $hn$ variables resolves on each at most once per path.

The transformation needs the parameter: the paper leaves open whether regular resolution *strictly* effectively simulates resolution, with $f$ depending on $\Gamma$ alone. It derives three corollaries. Regular resolution is not closed under substitutions, since mapping every $W[x,j]$ back to $x$ turns the easy formulas $f(\Gamma_n,h_n)$ into formulas $\Gamma_n$ that need exponential regular refutations by the [separation of regular from general resolution](../../resolution-separations-and-supercritical-tradeoffs/ajpu-regular-vs-general.md). If regular resolution is weakly automatable, so is resolution. If regular resolution is [automatable](../../automatability-of-proof-systems/automatable-proof-system.md), so is resolution: run the automating algorithm on $f(\Gamma,r)$ for $r=0,1,2,\dots$ within its time bound and substitute back, since resolution is p-closed under substitutions. This recovers, without inspecting its proof, the extension to regular resolution of the [Atserias–Müller theorem](../../automatability-of-proof-systems/atserias-muller.md) that automating resolution is NP-hard.

## Depends on

- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Cook-Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Sam Buss, Emre Yolcu, "Regular Resolution Effectively Simulates Resolution", *Information Processing Letters*, 2024, doi:10.1016/j.ipl.2024.106489 (Definition 1.1, Definitions 2.2 and 2.4, Remark 2.3, Theorem 3.1 with the bounds in its proof, Question 3.2, Corollaries 4.2, 4.5 and 4.6).
