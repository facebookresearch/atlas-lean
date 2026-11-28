# Top-$k$ aggregated goal-directed score

A goal-directed generator is judged on its best molecule and on the quality of its best hundred at once. The aggregate averages the top-1, top-10 and top-100 means, so a single lucky hit cannot carry a model.

Let a generator supply at least one hundred proposals and let $s_1 \ge s_2 \ge \dots \ge s_{100}$ be the scores of its hundred best under a fixed scoring function with values in $[0,1]$. The aggregated benchmark score is

$$
S = \frac{1}{3}\left( s_1 + \frac{1}{10}\sum_{i=1}^{10} s_i + \frac{1}{100}\sum_{i=1}^{100} s_i \right) .
$$

Each of the three terms is a mean of a prefix of a decreasing sequence, so each lies in $[0,1]$ and they decrease in the prefix length; hence $S \in [0,1]$, $S \le s_1$, and $S = 1$ exactly when all hundred scores equal $1$. Both facts are consequences of the display, not guarantees about a generator.

Scope. This page states the $1/10/100$ instance. The source applies a different cutoff to some tasks, for instance the top $159$ scores for an isomer task with $159$ admissible targets, and prints no rule for filling a short list, so a run with fewer than a hundred proposals is outside this statement rather than padded. Whether equivalent proposals are deduplicated before sorting is likewise an implementation convention, and it changes the value.

## Depends on

None.

## Proof depends on

None.

## Expansion

A formal development takes a decreasing vector in $[0,1]^{100}$, defines $S$ by the display, and proves the bounds from the monotonicity of prefix means of a decreasing sequence, which also gives $S \le s_1$ and the equality case. A variant with a general cutoff $K$ in place of $100$ is the same statement with the three prefix lengths given as parameters.

## Context

Undergraduate to graduate; a benchmark aggregation rule from Brown, Fiscato, Segler and Vaucher, reported by the goal-directed generators and genetic algorithms of this chapter.

## Sources

- Nathan Brown, Marco Fiscato, Marwin H. S. Segler and Alain C. Vaucher, *GuacaMol: Benchmarking Models for de Novo Molecular Design*, Journal of Chemical Information and Modeling 59 (2019) 1096–1108, Appendix, goal-directed implementation details (the top-1, top-10 and top-100 aggregation) and the benchmark table, where isomer tasks use their own cutoff. DOI [10.1021/acs.jcim.8b00839](https://doi.org/10.1021/acs.jcim.8b00839), arXiv:[1811.09621v2](https://arxiv.org/abs/1811.09621v2).
