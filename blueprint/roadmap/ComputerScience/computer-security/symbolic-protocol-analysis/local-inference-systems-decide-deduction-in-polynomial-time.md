# Local inference systems have polynomial-time intruder deduction

An inference system $\mathcal I$ on [terms](dolev-yao-terms-and-deduction.md) is *local* if for every finite set of terms $S$ and term $t$ with $S \vdash_{\mathcal I} t$
there is a proof tree of $S \vdash_{\mathcal I} t$ all of whose labels lie in $\mathrm{st}(S \cup \{t\})$.

**Theorem.** Let $\mathcal I$ be a local inference system for which one saturation round is computable in polynomial time: given finite sets of terms $S'$ and
$U$, the set $\{u \in U \mid S' \vdash^1_{\mathcal I} u\}$ of terms of $U$ obtained from $S'$ by one rule application is computable in time polynomial in the sizes of $S'$
and $U$. Then the intruder deduction
problem for $\mathcal I$ is decidable in polynomial time: it is in [P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md).

The algorithm sets $S_0 = S$ and $S_{i+1} = S_i \cup (\{u \mid S_i \vdash^1_{\mathcal I} u\} \cap \mathrm{st}(S \cup \{t\}))$, stops at a fixed point, reached after at most
$|\mathrm{st}(S \cup \{t\})|$ rounds, and checks whether $t$ was reached; locality makes it correct. Locality alone does not suffice: for a noncomputable set $K$ of
naturals, the rules $a / b_n$ for $n \in K$ form a local system with an undecidable deduction problem.

## Depends on

- [Dolev–Yao terms and intruder deduction](dolev-yao-terms-and-deduction.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 3.3, Definition 3.6 (local inference system) and Theorem 3.1 with its proof, which uses that each saturation step is computable in polynomial time.
