# Reasoning with finitely recursive logic programs is r.e.-complete

For disjunctive logic programs with function symbols in which every ground atom depends on only finitely many ground atoms, inconsistency checking and skeptical entailment of ground formulas under the stable model semantics are r.e.-complete, already for normal programs. Credulous entailment is co-r.e.-complete.

**Setting (Baselice, Bonatti and Criscuolo).** A *disjunctive program* is a finite set of rules $A_1 \vee \dots \vee A_m \leftarrow L_1, \dots, L_n$ ($m > 0$, $n \ge 0$) whose $A_j$ are atoms and whose $L_i$ are atoms or negated atoms $\mathit{not}\, A$; terms may contain function symbols. It is *normal* if every head has one atom. Its [stable models](stable-models-of-disjunctive-programs.md) are the Herbrand interpretations that are minimal models of the Gelfond–Lifschitz reduct of its ground instantiation $\mathrm{Ground}(P)$, which may be infinite. $P$ is *inconsistent* if it has no stable model; a closed formula is a *skeptical* consequence of $P$ if every stable model satisfies it, and a *credulous* consequence if some stable model does. The *dependency graph* $DG(P)$ has the ground atoms as vertices and an edge from $A$ to $B$ whenever some rule of $\mathrm{Ground}(P)$ has $A$ in its head and $B$ in its body (positively or negatively) or in its head. $P$ is *finitely recursive* if each ground atom reaches only finitely many ground atoms in $DG(P)$. Whether a program is finitely recursive is itself undecidable (Bonatti, as cited after Definition 2.1 of the source), so in the problems below the input program is promised to be finitely recursive.

**Theorem (Baselice, Bonatti and Criscuolo).**

1. For disjunctive finitely recursive programs, inconsistency checking and deciding whether a ground formula is a skeptical consequence are semidecidable.
2. Deciding whether a normal finitely recursive program is inconsistent is r.e.-hard, and so is deciding whether a normal finitely recursive program skeptically entails a ground formula.
3. Deciding whether a disjunctive finitely recursive program credulously entails a ground formula is co-r.e.-complete.

Finitely recursive programs extend finitary programs, which additionally have only finitely many odd-cyclic ground atoms and for which ground queries are decidable. Without the finite-recursion condition, the stable model semantics of programs with function symbols is $\Pi^1_1$-hard.

## Depends on

- [Stable models of disjunctive programs with function symbols](stable-models-of-disjunctive-programs.md)
- [The arithmetical class $\Sigma_n$](../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Recognizability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Co-recognizability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The upper bounds use a compactness property: a finitely recursive program has a sequence of finite modules $P_1 \subseteq P_2 \subseteq \cdots$ of its ground instantiation such that $P$ is inconsistent, or skeptically entails a ground formula, exactly when some finite $P_k$ does, which a procedure can detect by enumerating the modules. For the lower bound, skeptical entailment of an existentially quantified formula $\exists F$ from a normal finitary program, which is r.e.-complete by Bonatti's earlier work, reduces to inconsistency: add, for each clause of the conjunctive normal form of $\neg F$, a constraint-like rule $p_i(\vec{x}_i) \leftarrow \mathit{not}\, l_{i1}, \mathit{not}\, l_{i2}, \dots, \mathit{not}\, p_i(\vec{x}_i)$, which removes exactly the stable models satisfying an instance of $F$. Inconsistency in turn reduces to skeptical entailment of a fresh atom, and credulous entailment of $F$ is the complement of skeptical entailment of $\neg F$.

## Sources

- Sabrina Baselice, Piero A. Bonatti and Giovanni Criscuolo, "On finitely recursive programs", Theory and Practice of Logic Programming 9(2), pp. 213–238, 2009, <https://doi.org/10.1017/S147106840900372X>; Section 2 (stable models, Definition 2.1 of finitely recursive programs) and Theorems 5.1, 5.3, 5.4, 5.5 and Corollary 5.6 of arXiv:0901.2850v1, read at <https://arxiv.org/abs/0901.2850v1>.
