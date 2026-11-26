# Dolev–Yao intruder deduction is decidable in polynomial time

**Corollary.** The intruder deduction problem for the [Dolev–Yao inference system](dolev-yao-terms-and-deduction.md) is decidable in polynomial time: given a finite set of
terms $S$ and a term $t$, whether $S \vdash_{\mathcal I_{\mathrm{DY}}} t$ is decidable in time polynomial in the size of $S$ and $t$.

The system is local, and with its seven rules one saturation round only tries each rule on pairs of known terms, which takes polynomial time.

## Depends on

- [Dolev–Yao terms and intruder deduction](dolev-yao-terms-and-deduction.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Local inference systems have polynomial-time intruder deduction](local-inference-systems-decide-deduction-in-polynomial-time.md)
- [The Dolev–Yao inference system is local](the-dolev-yao-inference-system-is-local.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 3.3, Corollary 3.2.
