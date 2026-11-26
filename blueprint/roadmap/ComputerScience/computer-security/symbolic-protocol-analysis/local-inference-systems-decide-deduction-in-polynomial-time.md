# Local inference systems have polynomial-time intruder deduction

An inference system $\mathcal I$ on [terms](dolev-yao-terms-and-deduction.md) is *local* if for every finite set of terms $S$ and term $t$ with $S \vdash_{\mathcal I} t$
there is a proof tree of $S \vdash_{\mathcal I} t$ all of whose labels lie in $\mathrm{st}(S \cup \{t\})$.

**Theorem.** For a local inference system $\mathcal I$, the intruder deduction problem is decidable in polynomial time: it is in [P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md).

The algorithm saturates $S$ within the finite set $\mathrm{st}(S \cup \{t\})$ by one-step deductions, which reaches a fixed point after at most
$|\mathrm{st}(S \cup \{t\})|$ rounds, and then checks whether $t$ was reached.

## Depends on

- [Dolev–Yao terms and intruder deduction](dolev-yao-terms-and-deduction.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 3.3, Definition 3.6 (local inference system) and Theorem 3.1 with its proof.
