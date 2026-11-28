# Fuzzy description logic with residuated implication

The fuzzy description logic $*$-ALE interprets concepts as fuzzy sets with values in $[0, 1]$, conjunction by a continuous t-norm $\otimes$ and implication by its residuum; ontologies consist of graded assertions and graded general concept inclusions, and consistency can be taken with respect to all, witnessed, quasi-witnessed, strongly witnessed or finite models.

**T-norms.** A *t-norm* is an associative, commutative, monotone operation $\otimes$ on $[0, 1]$ with unit $1$; if it is continuous, its *residuum* $\Rightarrow$ is the unique operation with $z \leq x \Rightarrow y$ iff $x \otimes z \leq y$. Every continuous t-norm is an ordered sum of copies of the Łukasiewicz and product t-norms on disjoint subintervals $(a_i, b_i)$. For $q \in (0, 1]$, $\otimes$ *$q$-starts with the product t-norm* if one summand is the product t-norm on $(0, q)$; then $x \otimes y = xy/q$ for $x, y \in [0, q]$. The product t-norm $x \cdot y$ itself $1$-starts with it, and for each $q \in (0, 1)$ there are uncountably many continuous t-norms that $q$-start with it.

**Syntax.** Concepts are $C ::= A \mid \bot \mid \top \mid C_1 \sqcap C_2 \mid C_1 \to C_2 \mid \exists r.C \mid \forall r.C$ with $A$ a concept name and $r$ a role name. An ABox is a finite set of assertions $\langle a : C \bowtie q\rangle$ and $\langle (a, b) : r \bowtie q\rangle$ with $\bowtie \in \{\geq, =\}$ and $q \in [0, 1] \cap \mathbb{Q}$; a TBox is a finite set of general concept inclusions (GCIs) $\langle C \sqsubseteq D \geq q\rangle$; an ontology is a pair of an ABox and a TBox.

**Semantics.** An interpretation $\mathcal{I}$ has a nonempty domain $\Delta$, maps individuals to elements, concept names to functions $\Delta \to [0, 1]$ and role names to functions $\Delta \times \Delta \to [0, 1]$. Complex concepts are interpreted by $(C_1 \sqcap C_2)^\mathcal{I} = C_1^\mathcal{I} \otimes C_2^\mathcal{I}$, $(C_1 \to C_2)^\mathcal{I} = C_1^\mathcal{I} \Rightarrow C_2^\mathcal{I}$, $(\exists r.C)^\mathcal{I}(\delta) = \sup_\gamma r^\mathcal{I}(\delta, \gamma) \otimes C^\mathcal{I}(\gamma)$ and $(\forall r.C)^\mathcal{I}(\delta) = \inf_\gamma r^\mathcal{I}(\delta, \gamma) \Rightarrow C^\mathcal{I}(\gamma)$. A GCI $\langle C \sqsubseteq D \geq q\rangle$ is true if $\inf_\delta (C^\mathcal{I}(\delta) \Rightarrow D^\mathcal{I}(\delta)) \geq q$. A model is *witnessed* if every supremum for $\exists r.C$ and every infimum for $\forall r.C$ is attained at some element; *weakly witnessed* if this is true for $\exists$; *quasi-witnessed* if it is true for $\exists$, and for $\forall$ whenever the value is nonzero; *strongly witnessed* if it is witnessed and moreover, for all concepts $C$ and $D$, not only those in the ontology's GCIs, the infimum of $C^\mathcal{I}(\eta) \Rightarrow D^\mathcal{I}(\eta)$ over $\eta$ is attained (condition (wit3) of Section 3 of the source). An ontology is *consistent* (resp. witnessed consistent, and so on) if it has a model (of that kind).

## Depends on

- [ALC syntax, semantics and reasoning tasks](../../alc-syntax-semantics-and-reasoning-tasks.md)

## Proof depends on

None.

## Expansion

Strongly witnessed consistency implies witnessed, quasi-witnessed and weakly witnessed consistency, in that order. Witnessed models were introduced so that tableau algorithms can create one successor realizing each existential restriction; with GCIs some of these fuzzy DLs lack the finite model property.

## Sources

- F. Baader and R. Peñaloza, "On the undecidability of fuzzy description logics with GCIs and product t-norm", in *Frontiers of Combining Systems (FroCoS 2011)*, Lecture Notes in Computer Science 6989, Springer, 2011, pp. 55–70, doi:10.1007/978-3-642-24364-6_5; read as the open-access copy <https://boa.unimib.it/bitstream/10281/257917/1/BaPe-FroCoS11.pdf>: Section 2 (t-norms, residua, ordered sums and Definition 2) and Section 3 (syntax and semantics of $*$-ALE and the kinds of witnessed models).
