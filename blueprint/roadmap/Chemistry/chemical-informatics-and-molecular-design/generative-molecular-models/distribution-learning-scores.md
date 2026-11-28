# Validity, uniqueness and novelty of a generated molecule set

Three separate experiments measure how well a generator reproduces a reference library: one counts samples that parse, one counts distinct molecules among valid samples, and one counts distinct molecules absent from the reference set. Each score is defined on a run of its own protocol that completes.

Fix a sample size $N \ge 1$ (the source uses $N = 10\,000$), a parser deciding validity, a canonical form deciding identity of molecules, and the reference set, which in the source is the processed ChEMBL dataset rather than the model's training set. Each score comes from its own sampling run:

- *Validity*: draw $N$ samples; with $V$ of them parsing to a molecule, the score is $V/N$.
- *Uniqueness*: draw until $N$ valid molecules are collected; with $U$ distinct canonical forms among them, the score is $U/N$.
- *Novelty*: draw until $N$ distinct canonical forms are collected; with $W$ of them absent from the reference set, the score is $W/N$.

Each score lies in $[0,1]$, and each is defined only when its own run completes; the source fixes no attempt cap or fallback, so a run that does not complete leaves its score undefined rather than zero. On a completed uniqueness run $U \ge 1$, so that score is at least $1/N$.

Completion is probabilistic. For independent draws from a fixed law, a positive probability of a valid molecule makes the uniqueness run finish almost surely, and at least $N$ molecules of positive probability make the novelty run finish almost surely; dependent draws can repeat one molecule forever. A high score is not guaranteed by matching the reference law either: drawing independently and uniformly from a valid reference set of $M \ge N \ge 2$ molecules repeats the previous molecule with probability $1/M$ at each draw, so uniqueness falls below $1$ on such a run, while novelty, if its run completes, is $0$ because every molecule drawn lies in the reference set.

## Depends on

None.

## Proof depends on

- [Second Borel–Cantelli lemma for independent measurable sets](../../../Probability/foundations/borel-cantelli-lemmas/second-borel-cantelli-lemma/measure-limsup-eq-one.md)

## Expansion

A formal development models the generator as a probability measure on strings, validity as a decidable predicate and canonical form as a map from valid strings to molecules; the three scores are ratios of cardinalities of finite samples, each defined on a completed run of its own protocol. Almost-sure completion follows from the second Borel–Cantelli lemma applied to the independent events that the $n$-th draw is valid, whose probabilities sum to infinity under the positivity hypothesis, and likewise for the $N$ distinct molecules of positive probability in the novelty run; an explicit geometric-tail estimate gives the same conclusion.

## Context

Undergraduate to graduate; benchmark definitions, not theorems. Brown, Fiscato, Segler and Vaucher fixed them as the distribution-learning part of a standard suite, and the generators of this chapter report them.

## Sources

- Nathan Brown, Marco Fiscato, Marwin H. S. Segler and Alain C. Vaucher, *GuacaMol: Benchmarking Models for de Novo Molecular Design*, Journal of Chemical Information and Modeling 59 (2019) 1096–1108, Appendix, implementation details of the distribution-learning benchmarks, which specify the three separate sampling protocols and the ChEMBL comparator. DOI [10.1021/acs.jcim.8b00839](https://doi.org/10.1021/acs.jcim.8b00839), arXiv:[1811.09621v2](https://arxiv.org/abs/1811.09621v2).
