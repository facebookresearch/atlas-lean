# Uniform error and regret for selecting the best of finitely many simulated alternatives

Let $X$ be a finite nonempty set, $n \ge 1$, $a < b$ and $\varepsilon > 0$. For each $x \in X$ let $\hat C(x)$ be the average of $n$ independent almost-everywhere measurable real functions (replications) on a probability space, with values in $[a, b]$ almost surely and mean $C(x)$; replications for different $x$ may be dependent. Then $P(\max_x |\hat C(x) - C(x)| \ge \varepsilon) \le 2|X| \exp(-2n\varepsilon^2/(b-a)^2)$, and on the complementary event every minimizer $\hat x$ of $\hat C$ satisfies $C(\hat x) - \min_x C(x) < 2\varepsilon$.

The same holds for every $n \ge 0$, all real $a$ and $b$, and every $\varepsilon \ge 0$, reading an average of no replications as $0$ and a quotient by $0$ as $0$: the bound is then at least $1$ when $n = 0$ or $a = b$, no replication takes values in $[a, b]$ almost surely when $a > b$, and the complementary event is empty when $\varepsilon = 0$.

The replications need not be measurable, so neither need the event $\max_x |\hat C(x) - C(x)| \ge \varepsilon$; it is null-measurable, and $P$ denotes the probability in the completion of the probability space. The claim about minimizers holds at every outcome of the complementary event.

## Background

- [Uniform deviation for a finite class](../../machine-learning/generalization-bounds-and-concentration/finite-class-uniform-deviation.md): the same argument for a finite class of predictors evaluated on one shared sample.

## Sources

- S. Asmussen and P. W. Glynn, *Stochastic Simulation: Algorithms and Analysis*, Springer, 2007: background on estimating costs by simulation, not a source for this statement.
- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF dated 26 May 2025 at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>: Section 1.2.1, Corollary 1.1 and the first remark after it (the two-sided Hoeffding inequality for an average of independent variables in $[a, b]$); Section 4.4.3 (the union bound over a finite class); Section 4.4, equation (4.10) and the sentence after it (the excess risk of an empirical risk minimizer is at most twice the largest deviation). These are the ingredients of the proof, not a source for the whole statement, which follows from them.
