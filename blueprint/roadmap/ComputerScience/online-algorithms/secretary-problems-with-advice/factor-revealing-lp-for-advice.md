# A unified factor-revealing LP for secretaries with advice

For every signaling structure with a finite signal space $S$ (so that every signal value has a well-defined probability) satisfying *Non-Filtering* (conditioned on candidate $j$ being best so far with signal $s_j$, the information available at time $j$ is independent of whether a later candidate $i$ is best so far and of its signal) and *History-Irrelevance* (conditioned on candidate $i$ being best so far with signal $s_i$, the event that $i$ is the overall best is independent of the information available at time $i$), the optimal win probability equals the value of a linear program generalizing the secretary LP:

$$
\max \sum_{i, s} a(i, s)\, z(i, s) \quad \text{s.t.} \quad z(i, s) \le 1 - \sum_{j < i} \sum_{s'} c(i, s, j, s')\, z(j, s'), \quad z \ge 0,
$$

where $z(i, s)$ is the probability of accepting the candidate at position $i$ with signal $s$ given that it is the best so far, $a(i, s)$ is the probability that the overall best candidate sits at position $i$ with signal $s$, and $c(i, s, j, s')$ is the probability that the candidate at position $j$ with signal $s'$ is best so far given that the candidate at position $i > j$ with signal $s$ is. Every feasible $z$ is realized by a stopping policy, and an optimal policy is memoryless: it rejects every candidate that is not best so far, and accepts a best-so-far candidate at position $i$ with signal $s_i$ with a probability that depends only on $(i, s_i)$. The record condition is part of the decision rule: a rule using the signal alone, without checking that the candidate is best so far, is not of this form. Solving the LP and its dual gives tight analyses and optimal policies for secretaries with samples and for a noisy binary advice model. The LP is a statement about discrete signals: with one candidate and a signal uniform on $[0,1]$ the win probability is $1$, yet every singleton probability $a(1,s)$ is $0$. For qualities drawn from a known distribution (the full-information problem of Gilbert and Mosteller, with optimal win probability tending to approximately $0.5801$), whose signals (quantiles) are continuous, Dütting, Lattanzi, Paes Leme and Vassilvitskii instead view it as the limit $k \to \infty$ of the problem with $k$ samples (finite signal space $\{0, \dots, k\}$) and replace $a$ and $c$ by densities, $a(i,q) = q^{n-1}\,dq$ and $c(i,q,j,q') = \frac{1}{q}\big(\frac{q'}{q}\big)^{j-1} dq'$, which gives a functional LP whose dual solution, obtained by backward induction, recovers Gilbert and Mosteller's thresholds; this continuous version is a formal limit of the finite LPs, not an instance of the theorem above.

## Proof sketch

By the two properties, whether the current candidate is best so far with signal $s$ has a conditional law that does not depend on the policy's past behavior beyond having not stopped, so the stopping constraints are linear in $z$ exactly as in the classical case, and any policy induces a feasible $z$ with objective equal to its win probability. Conversely a feasible $z$ is implemented by rejecting every candidate that is not best so far and accepting a best-so-far candidate at position $i$ with signal $s$ with the appropriately rescaled probability. Optimal dual solutions certify optimality of threshold policies in signal space; for the full-information model the functional LP obtained as the $k \to \infty$ limit of the $k$-sample LPs recovers Gilbert and Mosteller's thresholds.

## Depends on

- [Secretary problems with advice](secretary-with-advice-model.md)

## Proof depends on

- [Linear-programming characterization of the classical secretary problem](secretary-lp.md)

## Sources

- Paul Dütting, Silvio Lattanzi, Renato Paes Leme, Sergei Vassilvitskii, "Secretaries with Advice", EC (2021); Mathematics of Operations Research 49(2) (2024), arXiv:2011.06726, Section 1.1 (signal space), the examples of Section 2.1, Figure 1, Definitions 6 and 7, Propositions 9 and 10, Theorem 8, and Corollary 18 with the paragraph before it (Gilbert and Mosteller as a limit).
