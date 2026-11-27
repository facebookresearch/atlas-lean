# Election control problems

Fix a voting system that maps an election, a finite candidate set together with voters' preferences,
to its set of winners; a candidate is the unique winner when it is the only winner. Each control
problem below is a decision problem with a constructive question (can the chair make the
distinguished candidate $c$ the unique winner?) and a destructive question (can the chair make $c$ not
the unique winner?):

- **adding candidates:** given qualified candidates $C \ni c$, spoiler candidates $D$ and voters over
  $C \cup D$, is there a set of spoilers from $D$ whose entry achieves the goal (no bound on the number
  of spoilers);
- **deleting candidates:** given $C \ni c$, voters and an integer $k$, is there a set of at most $k$
  candidates, not containing $c$ in the destructive case, whose removal achieves the goal;
- **adding voters:** given registered voters $V$, unregistered voters $W$ and $k \le \lvert W \rvert$,
  is there a set of at most $k$ voters from $W$ whose registration achieves the goal;
- **deleting voters:** given voters $V$ and $k \le \lvert V \rvert$, is there a set of at most $k$
  voters whose removal achieves the goal.

A voting system is **immune** to a type of control if the chair can never, by that type of control,
change $c$ from not being the unique winner to being the unique winner (constructive) or from being the
unique winner to not being the unique winner (destructive); otherwise it is **susceptible**. A
susceptible system is **vulnerable** if the corresponding decision problem is solvable in polynomial
time, and **resistant** if it is NP-complete (Definition 3.1 of the cited paper; for the systems studied there
the winner can be computed in polynomial time, so these problems are in NP, and NP-hardness and
NP-completeness coincide). Susceptibility alone does not imply vulnerability. Elections are encoded as a
candidate list and a list of ballots, one preference order per voter, and complexity is measured in this
encoding.

## Expansion

This node states a precise definition. A good expansion adds a page for the pending prerequisite below and
links it under the dependency sections, and gives each of the following variants of the original scope its own
definition page with its own source; they are different problems from the ones above, not rewordings:

1. **Bounded candidate addition:** given $C \ni c$, spoilers $D$, voters over $C \cup D$ and an integer $k$, is there a
   set of at most $k$ spoilers whose entry achieves the goal. It differs from the unbounded version: with
   registered candidates $c, d$, spoilers $a, b$ and plurality voting over the five ballots $c > d > a > b$ (twice),
   $d > a > b > c$, $a > d > b > c$ and $b > d > a > c$, adding both spoilers makes $c$ the unique winner while adding
   either one alone does not.
2. **Destructive control against winning at all:** the goal is that $c$ is not a winner, rather than not the unique
   winner; an election whose winners are exactly $c$ and another candidate separates the two goals.
3. **Partition of candidates and partition of voters,** each with its tie-handling rule.

- Statement prerequisite: standard voting rules (plurality, Condorcet and the other systems to which the definitions are applied).

## Sources

- E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, *Anyone but him: the complexity of precluding an
  alternative*, Artificial Intelligence 171 (2007); arXiv:cs/0507027, Section 3 (the control problems
  and Definition 3.1 of immunity, susceptibility, vulnerability and resistance), following Bartholdi,
  Tovey and Trick (1992). <https://arxiv.org/abs/cs/0507027>
