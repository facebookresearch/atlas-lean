# Linear programs for extremal reachability probabilities

Let $M$ be a finite [Markov decision process](markov-decision-processes-and-adversaries.md) with target set $T$ and [qualitative sets](qualitative-reachability-by-graph-analysis.md) as computed by graph analysis.

- The linear program: maximize $\sum_{s \in S} x_s$ subject to $x_s = 1$ for $s \in S^1_{\min}$, $x_s = 0$ for $s \in S^0_{\min}$, and $x_s \le \sum_{s'} \delta(s, a)(s')\, x_{s'}$ for all other states $s$ and all $a \in A(s)$, has a unique solution, and it is $x_s = \Pr^{\min}_s(\mathit{reach}(T))$.
- The linear program: minimize $\sum_{s \in S} x_s$ subject to $x_s = 1$ for $s \in S^1_{\max}$, $x_s = 0$ for $s \in S^0_{\max}$, and $x_s \ge \sum_{s'} \delta(s, a)(s')\, x_{s'}$ for all other states $s$ and all $a \in A(s)$, has a unique solution, and it is $x_s = \Pr^{\max}_s(\mathit{reach}(T))$.

## Depends on

- [Extremal reachability probabilities](extremal-reachability-probabilities.md)
- [Linear program](../../../Geometry/convex-geometry/linear-programming/linear-program.md)
- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)
- [Qualitative reachability by graph analysis](qualitative-reachability-by-graph-analysis.md)

## Proof depends on

- [Bellman equations for minimum reachability probabilities](bellman-equations-for-minimum-reachability-probabilities.md)
- [Maximum reachability probabilities are the least Bellman solution](maximum-reachability-probabilities-are-the-least-bellman-solution.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 4.2 (linear programming).
