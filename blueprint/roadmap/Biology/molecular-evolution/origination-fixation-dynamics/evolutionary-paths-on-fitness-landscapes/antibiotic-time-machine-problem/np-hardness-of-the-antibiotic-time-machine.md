# NP-hardness of the antibiotic time machine

**Problem.** Bacterial genotypes form a finite state set $S$ of size $d$, state $1$ being the wild type. Each of $K$ available antibiotics acts on a population as a row-stochastic $d\times d$ matrix $T$, with $t_{ij}$ the probability that a bacterium of genotype $i$ has genotype $j$ after treatment with that drug (computed, e.g., from a fitness landscape under strong-selection weak-mutation dynamics). Starting from the pure wild-type population $s=(1,0,\dots,0)$, a treatment plan of length $N$ is a sequence $T_1,\dots,T_N$ from the set $\mathcal T$ of drug matrices. The **time machine** problem asks for the plan that maximizes the probability of returning to the wild type,

$$\mathcal{TM}(d,K,N)=\max_{T_1,\dots,T_N\in\mathcal T}\ s\,T_1T_2\cdots T_N\,s^{\top},$$

so as to reverse resistance mutations that earlier treatments may have selected. The **decision version** asks, for a threshold $\alpha\in[0,1]$, whether some plan achieves $s\,T_1\cdots T_N\,s^\top\ge\alpha$. There are $K^N$ plans, so enumeration is exponential in $N$.

**Theorem.** The time machine decision problem is NP-hard, already for $\alpha=1$; consequently the time machine optimization problem is NP-hard.

## Expansion

The proof reduces $3$-SAT to the decision problem with $\alpha=1$. From a formula in variables $x_1,\dots,x_n$ with $m$ clauses one builds, in polynomial time, a state space and a set of transition matrices together with a plan length $N$ such that the product $T_1\cdots T_N$ can return all of the wild-type mass to the wild type only if the choices of matrices encode a consistent truth assignment satisfying every clause. If the formula is satisfiable, an explicit sequence of matrices sends all weight back to $s$. Conversely, if some plan achieves return probability $1$, then for each variable the state carrying positive weight after $m+1$ steps determines a value $v_i$, and $(x_i=v_i)_i$ is a satisfying assignment, since any violated clause would divert positive mass away from the wild type permanently. As $3$-SAT is NP-complete, the decision problem is NP-hard, and the optimization problem, which answers the decision problem by comparing its optimum with $\alpha$, is NP-hard as well. Efficient algorithms may still exist for restricted instances, such as few drugs, short plans or special landscapes.

## Sources

- Ngoc M. Tran, Jed Yang, "Antibiotics Time Machine is NP-hard", published as "Antibiotics Time Machines Are Hard to Build", *Notices of the American Mathematical Society* 64 (2017), 1136–1140, <https://doi.org/10.1090/noti1590>; preprint arXiv:1505.02694, <https://doi.org/10.48550/arXiv.1505.02694>. Numbering of the arXiv version: Section 1 (problem (1) and decision version (2), Theorems 1 and 2), Section 2 (reduction construction from 3-SAT), Section 3 (Lemmas 3 and 4, proof of the main theorem).
