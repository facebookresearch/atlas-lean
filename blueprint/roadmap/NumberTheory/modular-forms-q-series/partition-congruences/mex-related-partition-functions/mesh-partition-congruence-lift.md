# Lifting partition congruences to mex partition functions

For a partition $\lambda$, a
positive integer $A$ and a natural number $c$, let $\operatorname{mex}_{A,c}(\lambda)$ be the
smallest positive integer congruent to $c$ modulo $A$ that is not a part of $\lambda$, and let
$p_{A,c}(N)$ be the number of partitions $\lambda$ of $N$ with
$\operatorname{mex}_{A,c}(\lambda) \equiv c \pmod{2A}$. Let $p(N)$ be the number of partitions of
$N$. Let $m$, $a$ and $b$ be natural numbers with $m \ge 1$ and $b < a$, and suppose that $m$
divides $p(an + b)$ for every natural number $n$. Then for every integer $t \ge 1$ and every
natural number $n$, $m$ divides both $p_{at,at}(an + b)$ and $p_{2at,at}(an + b)$.

Because $b < a$, the hypothesis covers the whole residue class of $b$ modulo $a$; for $b \ge a$
the lift would need $p$ at arguments below $b$, which the hypothesis does not cover.

The proof follows the Andrews–Newman mex decomposition used by Barman and Singh: remove one copy
of every forced earlier mex candidate. The exact-mex fibers then telescope, while every removed
prefix sum remains a multiple of $a$.

## Sources

- Rupam Barman and Ajit Singh, "Mex-Related Partition Functions of Andrews and Newman," Journal of Integer Sequences 24 (2021), Article 21.6.3, Theorem, lines 172–182, https://cs.uwaterloo.ca/journals/JIS/VOL24/Barman/barman3.tex
