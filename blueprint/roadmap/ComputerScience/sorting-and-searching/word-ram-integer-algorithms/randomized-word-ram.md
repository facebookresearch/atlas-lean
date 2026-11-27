# Randomized word RAM

A **randomized word RAM** with word size $w$ is a word RAM (unit-cost arithmetic, comparison, bitwise and indirect-addressing instructions on $w$-bit words, with an unbounded array of memory cells) extended by one instruction $\mathrm{rand}(m)$ that, for a register value $m \ge 1$, writes into a register a value drawn uniformly from $\{0, 1, \dots, m-1\}$, independently of all earlier draws.

A program $P$ on input $x$ (stored in the first $|x|$ cells, all other cells zero) induces a probability distribution over finite runs. $P$ **runs in time $T$** if every run, for every outcome of the draws, halts within $T$ instructions; its **output law** is the distribution of the value it halts with. Inputs are admitted only for word sizes with $2^w$ larger than every number the program stores, which forces $w = \Omega(\log n)$ for inputs of length $n$.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Las Vegas and Monte Carlo algorithms](../../randomized-algorithms/probabilistic-analysis-tools/las-vegas-and-monte-carlo-algorithms.md)

## Sources

- M. Mitzenmacher and E. Upfal, "Probability and Computing", 2nd ed., Cambridge University Press, 2017.
- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
