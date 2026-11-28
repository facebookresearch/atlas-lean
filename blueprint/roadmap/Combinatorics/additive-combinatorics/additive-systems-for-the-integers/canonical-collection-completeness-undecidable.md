# Completeness of Fractran-type canonical collections is undecidable

No algorithm decides, given a Fractran program, whether the canonical collection built from it is an additive system for the integers; completeness of that collection is equivalent to the program halting on every input.

Let $F=(F_1,\dots,F_m)$, $m\ge1$, be a Fractran program, a nonempty finite list of positive rationals. Its inputs are the nonnegative integers. On input $0$ the program halts immediately, before any fraction is tried. On a positive input $n$ one Fractran step replaces $n$ by $nF_j$ for the first $j$ such that $nF_j$ is an integer; the program halts on $n$ when no such $j$ exists, and it halts on an input when its trajectory of steps reaches such a number or $0$. Let $f_F:\mathbb N_0\to\mathbb N_0$ be given by $f_F(0)=0$, by $f_F(n)=nF_j$ when a step applies to $n>0$, and by $f_F(n)=0$ when the program halts on $n>0$ without a step; so $0$ is absorbing, and $f_F(n)=0$ marks halting, since a step from a positive integer gives a positive integer. Set $b=1+\lceil\max_jF_j\rceil$ and $b_i=b^{i+1}$. The *Fractran-type* [canonical collection](canonical-collections-for-the-integers.md) $\mathcal A_F$ has bases $(b_i)$ and the canonical system with $f_i(r)=f_F(r)$ for $0\le r<b_i-1$ and $f_i(b_i-1)=1$; it is determined by the finite data $F$.

**Theorem (Zabolotskii).**
1. A Fractran program $F$ halts on every input iff $\mathcal A_F$ is complete, that is, an [additive system](additive-systems-for-a-commutative-monoid.md) for $\mathbb Z$.
2. Consequently it is undecidable, given a Fractran program $F$, whether $\mathcal A_F$ is complete.

The source also gives a canonical collection whose completeness is equivalent to the Collatz conjecture (Theorem 1). For additive systems for $\mathbb N_0$, in contrast, de Bruijn's theorem describes all of them as contractions of mixed-radix number systems.

## Depends on

- [Canonical collections for the integers](canonical-collections-for-the-integers.md)
- [Additive systems for a commutative monoid](additive-systems-for-a-commutative-monoid.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

By Corollary 1 of the source, $\mathcal A_F$ is complete iff every integer's trajectory under the canonical system is eventually $0$. A trajectory value $n_i$ in $[0,b_i-1)$ continues as the Fractran trajectory of $n_i$ and reaches $0$ iff $F$ halts on $n_i$, while $n_i=b_i-1$ jumps to $1$. Every positive integer eventually enters such an interval because $n_{i+1}<n_i$ as long as $n_i\ge(b-1)b_i$, and every negative integer strictly increases along its trajectory until it becomes nonnegative. Conversely every $n\in\mathbb N$ is reached: the trajectory of $n\,b^{L(L+1)/2}$ with $L=\lceil\log_b(n+1)\rceil$ arrives at $n$ after $L$ steps without hitting an exceptional value. Hence completeness is equivalent to $F$ halting on every input. Part 2 follows because the universal halting problem for Fractran programs is undecidable, as Fractran is Turing complete (Conway). A good expansion links the undecidability of universal halting for Fractran programs.

## Sources

- Andrei Zabolotskii, "Additive systems for $\mathbb Z$ are undecidable", *Journal of Combinatorial Mathematics and Combinatorial Computing* 130:241–253, 2026, doi:[10.61091/jcmcc130-16](https://doi.org/10.61091/jcmcc130-16); read in arXiv:2508.17285v2, whose numbering is used here: Definition 6, Theorem 2 and its proof, Corollary 2, Section 2 (de Bruijn's theorem) and Theorem 1.
- John H. Conway, "FRACTRAN: a simple universal programming language for arithmetic", in *Open Problems in Communication and Computation*, Springer, 1987, the source of the universality of Fractran, as cited in the source above; not read here.
