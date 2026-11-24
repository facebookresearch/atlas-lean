# k-CNF is PAC learnable by elimination

Let $D$ be any probability distribution on labelled truth assignments of $t$ Boolean variables
under which some $k$-CNF function has error $0$ (the realizable case). For $m$ independent examples
from $D$, the probability that the elimination learner outputs a hypothesis whose error exceeds
$\varepsilon$ is at most $2^N (1 - \varepsilon)^m$, where $N$ is the number of clauses of at most
$k$ literals over the $t$ variables, so $N \le \sum_{j \le k} (2t)^j$.

Valiant proves learnability of $k$-CNF with $L(h, (2t)^{k+1})$ positive examples through his
Bernoulli-trial bound $L(h, S) \le 2h(S + \ln h)$; this statement replaces that argument by the
Occam bound for consistent learners, which applies because the elimination learner is consistent
with the $k$-CNF class. If $D$ is supported on the positive examples of the target, as in
Valiant's protocol, the error of the output is exactly the mass of the positive examples it
rejects, condition (ii) of his definition.

## Background

- [Valiant's Bernoulli-trial bound](../valiant-s-bernoulli-trial-bound/measure-real-sum-lt-lt-inv.md):
  the lemma through which Valiant himself bounds the number of examples in Theorem A; the statement
  here uses the Occam bound instead.

## Sources

- L. G. Valiant, *A theory of the learnable*, Communications of the ACM 27 (1984), 1134-1142, Section 4 (Proposition) and Section 5 (Theorem A).
- A. Blumer, A. Ehrenfeucht, D. Haussler and M. K. Warmuth, *Occam's razor*, Information Processing Letters 24 (1987), 377-380.
