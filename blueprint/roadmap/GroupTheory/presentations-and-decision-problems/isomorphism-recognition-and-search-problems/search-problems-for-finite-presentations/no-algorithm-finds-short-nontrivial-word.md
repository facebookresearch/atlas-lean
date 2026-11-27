# No algorithm finds a short non-trivial word in a non-trivial finitely presented group

For every fixed $k > 0$, no algorithm takes a finite presentation of a non-trivial group and outputs a word of length at most $k$ that is non-trivial in the group; for $k = 1$, no algorithm picks out a generator that is non-trivial.

Fix an integer $k > 0$. There is no algorithm that, on input of a finite presentation $P = \langle X \mid R \rangle$ of a non-trivial group $\overline{P}$, outputs a word $w \in W(X)$ of length at most $k$ that represents a non-trivial element of $\overline{P}$ (Theorem 4.2 of the source). In particular there is no algorithm that, on input of a finite presentation $P = \langle X \mid R \rangle$ of a non-trivial group, outputs a generator $x \in X$ that is non-trivial in $\overline{P}$ (Corollary 4.3).

Here $W(X)$ is the set of words over $X \cup X^{-1}$, a finite presentation $P = \langle X \mid R \rangle$ has finite sets $X$ and $R \subseteq W(X)$, and $\overline{P}$ is the group it presents. An algorithm for such a search problem need only succeed on the inputs satisfying the stated promise; the statements say that no algorithm succeeds on all of them.

Whether some algorithm outputs a non-trivial word of unbounded length from every finite presentation of a non-trivial group is left open by the source; a negative answer would settle Wiegold's question whether every finitely generated perfect group is the normal closure of one element.

## Depends on

- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Lemma 4.1: for fixed $k$, no algorithm takes $k + 1$ finite presentations, at least one of a non-trivial group, and discards one so that some remaining presentation still defines a non-trivial group. It follows from Rabin-type uniform constructions of presentations $\Pi_{n,x}$ that define the trivial group exactly when $x$ lies in the $n$-th recursively enumerable set $W_n$. Given $k + 1$ such presentations, an algorithm as in the theorem applied to their free product returns a non-trivial word of length at most $k$, which misses the generators of at least one factor; discarding that factor contradicts Lemma 4.1.

## Sources

- M. Chiodo, "Finding non-trivial elements and splittings in groups", Journal of Algebra 331 (2011), no. 1, 271–284, https://doi.org/10.1016/j.jalgebra.2010.12.013; arXiv:1002.2786v3 (Lemma 4.1, Theorem 4.2 and Corollary 4.3 of arXiv:1002.2786v3).
