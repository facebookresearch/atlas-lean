# Ancestral process of the weak seed-bank model

Let $N \ge 1$ and let $B$ be a random variable with law $\mathbb P(B = j) = b_j$ on $\{1, \dots, m\}$. In
the seed-bank model of Kaj, Krone and Lascoux each individual has its parent $B$ generations earlier,
chosen uniformly among the $N$ individuals of that generation, independently over individuals. Trace the
ancestral lines of a sample of $n \le N$ distinct individuals of generation $0$ back in time, one
generation per step. At step $k$ each line is an individual of one of the generations
$k, k + 1, \dots, k + m - 1$, and its residual age $r \in \{0, \dots, m - 1\}$ is its generation minus $k$.
The state records the partition of the sample into lines and the residual age of each line; positions
within a generation are drawn when a line arrives and need not be kept.
From step $k$ to step $k + 1$, each line in generation $k$ (residual age $0$) draws an independent copy of
$B$ and an independent uniform position among the $N$ individuals of generation $k + B$, and moves there;
a line that arrives at an occupied position merges with the line there, whether that line was placed
earlier or arrives in the same step. Lines in generations $k + 1, \dots, k + m - 1$ do not move.

This is the urn model of the source: generations are cells of $N$ slots, the lines are the balls, the
current $m$ generations form the window, and the step relocates the balls of the leftmost cell; the
numbers $X_j(k)$ of lines with residual age $j - 1$, $j = 1, \dots, m$, form its configuration process,
and the number of lines is the ancestor count $A_N(k) = X_1(k) + \dots + X_m(k)$. Given $X_1(k)$, the
numbers of relocated lines sent to the $m$ generations of the next window are multinomial with
parameters $X_1(k)$ and $b_1, \dots, b_m$. The transition kernel is a stochastic matrix on the finite set
of states: give the lines already in each generation distinct slot labels among the $N$ slots, draw
independent uniform slot labels for the relocating lines, and merge lines with equal labels; the law of
the resulting partition and residual ages does not depend on which distinct labels the existing lines
were given, so absolute positions need not be kept. For $B = 1$ the number of lines is the
[Wright–Fisher lineage-count chain](../../ancestral-lineage-counting-and-tavar-s-formula/wf-lineage-matrix.md). Two distinct
lines in the same generation are relocated to a common generation with probability $\sum_j b_j^2$ and
merge there with probability $\sum_j b_j^2 / N$.

## Depends on

- [Markov chain](../../../../Probability/markov-chains/chapman-kolmogorov-equations/is-markov-chain.md)

## Sources

- I. Kaj, S. M. Krone and M. Lascoux, "Coalescent theory for seed bank models", Journal of Applied Probability 38 (2001), 285–300, <https://doi.org/10.1239/jap/996986745>; author preprint dated 22 September 2000, Section 2 (the $m$-step seed-bank model, the space-time urn model, the configuration process $X(k)$ and the relocation law $\mathrm{Mult}(X_1(k); b_1, \dots, b_m)$).
