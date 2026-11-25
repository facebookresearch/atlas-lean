# Condorcet voting under candidate control

Condorcet voting elects the Condorcet winner, the candidate who beats every other candidate in a strict pairwise
majority comparison, if there is one, and otherwise has no winner. Its immunity to constructive control by adding
candidates is a separate result and is not part of this node. This node collects the remaining clause.

## Expansion

A sound expansion has a page for: **Condorcet voting is vulnerable to constructive control by deleting
candidates**, in the model of the election-control definitions (at most $k$ deletions, $c$ never deleted, the goal
that $c$ is the unique winner). It is susceptible: with candidates $c, d$ and a single voter preferring $d$ to $c$,
deleting $d$ makes $c$ the unique winner. The polynomial-time decision procedure: let $B$ be the set of candidates
other than $c$ that $c$ does not beat in a strict pairwise majority comparison; deleting candidates does not change
pairwise comparisons, so $c$ becomes the Condorcet winner after a deletion exactly when every candidate of $B$ is
deleted, and the instance is a yes-instance if and only if $\lvert B \rvert \le k$.

## Depends on

- [Election control problems](election-control-problems.md)

## Sources

- E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, *Anyone but him: the complexity of precluding an
  alternative*, Artificial Intelligence 171 (2007); arXiv:cs/0507027, Table 1 (Condorcet: immune to
  constructive control by adding candidates and vulnerable to constructive control by deleting
  candidates, both due to Bartholdi, Tovey and Trick 1992) and Section 3 (the control models).
  <https://arxiv.org/abs/cs/0507027>
