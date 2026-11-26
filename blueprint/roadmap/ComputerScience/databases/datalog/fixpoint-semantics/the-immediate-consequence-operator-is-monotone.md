# The immediate consequence operator is monotone

For a Datalog program $P$, the operator $T_P$ maps an instance $K$ over the schema of $P$ to the set of its immediate
consequences: the facts of $K$ over extensional relations together with the heads $\nu(A_0)$ of all rules
$A_0 \leftarrow A_1, \dots, A_n$ of $P$ and valuations $\nu$ with $\nu(A_1), \dots, \nu(A_n) \in K$. For an extensional
instance $I$ and an intensional instance $J$ over the domain $U$ of the [definition page](../datalog-programs-and-the-immediate-consequence-operator.md),
$T_P(I \cup J) = I \cup T_{P,I}(J)$.

**Lemma.** $T_P$ is monotone: if $K \subseteq K'$ then $T_P(K) \subseteq T_P(K')$. Consequently each $T_{P,I}$ is monotone on
intensional instances over $U$.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Section 12.3, Lemma 12.3.1(i) (p. 283).
- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 35.9 and Lemma 35.10(1) (pp. 324–325).
