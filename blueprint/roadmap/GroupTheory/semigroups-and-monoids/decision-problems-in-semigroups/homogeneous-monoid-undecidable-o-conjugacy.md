# Some finitely presented homogeneous monoid has undecidable o-conjugacy problem

There is a finitely presented monoid whose defining relations have sides of equal length, and even one whose relations have the same number of each generator on both sides, in which no algorithm decides whether two words are $o$-conjugate.

Elements $x, y$ of a monoid $M$ are $o$-conjugate, $x \sim_o y$, if there are $g, h \in M$ with $xg = gy$ and $hx = yh$; this is an equivalence relation. A presentation $\langle A \mid R \rangle$ of a monoid, with $A$ an alphabet and $R$ a set of relations $u = v$ between words over $A$, is homogeneous if $|u| = |v|$ for every relation, and multihomogeneous if, for every relation $u = v$ and every letter $a \in A$, the words $u$ and $v$ contain $a$ the same number of times; a monoid is (multi)homogeneous if it has such a presentation. Then (source):

1. there exists a finitely presented homogeneous monoid $M = \langle A \mid R \rangle$ in which the $o$-conjugacy problem is undecidable: no algorithm takes two words over $A$ and decides whether they represent $o$-conjugate elements (Theorem 4.1);
2. there exists a finitely presented multihomogeneous monoid with undecidable $o$-conjugacy problem (Theorem 4.8).

Homogeneous monoids have no zero, so for them $o$-conjugacy coincides with $c$-conjugacy, and a finitely presented homogeneous monoid has decidable word problem: its relations preserve length, so two words are equal only if they have the same length, and the finitely many words of that length over the finite alphabet can be searched exhaustively under the finitely many relations.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof takes a deterministic Turing machine with undecidable halting problem and builds a finite complete rewriting system with homogeneous rules that simulates its computation, so that the machine halts on an input $w$ exactly when the element representing the initial configuration on $w$ is $o$-conjugate to the element representing a fixed halting configuration. For the multihomogeneous case, the homogeneous monoid $M = \langle a_1, \dots, a_n \mid R \rangle$ is re-encoded over the two letters $x, y$ by $a_i \mapsto x^2 y^i x y^{n-i+1}$; the image presentation is multihomogeneous and the encoding embeds $M$ in the new monoid, which carries over the undecidability. By contrast, the source shows that $o$-conjugacy is decidable in the sylvester monoid and, with known results, in several other homogeneous monoids.

## Sources

- A. J. Cain and A. Malheiro, "Deciding conjugacy in sylvester monoids and other homogeneous monoids", International Journal of Algebra and Computation 25 (2015), no. 5, 899–915, https://doi.org/10.1142/S0218196715500241; read in arXiv:1404.2618v2 (Theorems 4.1 and 4.8 of arXiv:1404.2618v2, with the definitions in Section 2).
