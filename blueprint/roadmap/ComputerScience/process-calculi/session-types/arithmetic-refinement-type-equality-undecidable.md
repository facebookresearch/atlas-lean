# Equality of session types with arithmetic refinements is undecidable

For binary session types refined by natural-number indices, quantifiers and arithmetic constraints, deciding whether two types are equal under an arithmetic constraint is undecidable. Type definitions, internal choice and asserted constraints alone already suffice.

**Setting (Das and Pfenning).** Session types are given by

$$
A ::= \oplus\{\ell : A_\ell\}_{\ell \in L} \mid \&\{\ell : A_\ell\}_{\ell \in L} \mid A \otimes A \mid A \multimap A \mid \mathbf{1} \mid V[\bar{e}] \mid {?}\{\phi\}.A \mid {!}\{\phi\}.A \mid \exists n.\, A \mid \forall n.\, A,
$$

where $V[\bar{e}]$ is a type name from a finite set of (possibly recursive) type definitions applied to arithmetic expressions $e ::= i \mid e + e \mid e - e \mid i \times e \mid n$ over natural-number variables, ${?}\{\phi\}.A$ asserts and ${!}\{\phi\}.A$ assumes an arithmetic proposition $\phi$ (built from $=$, $>$, Boolean connectives and quantifiers over $\mathbb{N}$), and $\exists n$, $\forall n$ quantify over natural numbers. Indices range over $\mathbb{N}$ with ordinary subtraction: types are required to be *valid*, meaning that every index expression denotes a natural number under the constraints in force (for instance $n - 1$ only in a branch where $n > 0$ is known). Two closed types are *equal*, $A \equiv B$, if some *type bisimulation* relates them: after unfolding definitions, related types have the same outermost constructor and label sets with related continuations; related assertions or assumptions have propositions that are both true (with related continuations) or both false; and related quantified types have related instances for every $i \in \mathbb{N}$. For types with free variables $\vec{v}$ valid under a constraint $\mathcal{C}$, $\forall \vec{v}.\ \mathcal{C} \Rightarrow A \equiv B$ means that $A[\sigma] \equiv B[\sigma]$ for every ground substitution $\sigma$ of natural numbers satisfying $\mathcal{C}$.

**Theorem (Das and Pfenning).** Checking $\forall \vec{v}.\ \mathcal{C} \Rightarrow A \equiv B$ is undecidable: no algorithm decides it, given the type definitions, the constraint $\mathcal{C}$ and the types $A$ and $B$. The proof (Theorem 2 of the source) reduces from the non-halting problem for two-counter machines: the machine's computation is infinite iff the two constructed types are equal.

The authors note that the fragment containing only type definitions, internal choice and assertions suffices, and that the proof still applies when types are treated isorecursively. Because type checking uses type equality (for forwarding and channel passing), type checking is undecidable as well; the paper therefore gives a sound but incomplete coinductive algorithm.

## Depends on
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Proof sketch

The reduction is from the non-halting problem of two-counter machines. Type names indexed by the counter values encode machine configurations, and assertions on the indices let a type branch on whether a counter is zero, so that unfolding a type step by step follows the computation of the machine. Two types are constructed that behave identically as long as the computation runs and differ when it halts, so they are equal exactly when the machine does not halt.

## Sources

- Ankush Das and Frank Pfenning, "Session Types with Arithmetic Refinements", 31st International Conference on Concurrency Theory (CONCUR 2020), LIPIcs 171, Article 13, 2020, <https://doi.org/10.4230/LIPIcs.CONCUR.2020.13>; read in the extended version arXiv:2001.04439v3, <https://arxiv.org/abs/2001.04439v3>: the definitions and Theorem 2 in Section 4 ("Type Equality"), with Appendix B ("Type Equality"), in the numbering of that version.
