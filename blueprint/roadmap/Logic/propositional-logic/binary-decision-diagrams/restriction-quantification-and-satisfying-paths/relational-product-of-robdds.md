# Relational product of ROBDDs

Fix a variable ordering on two disjoint lists of variables $\bar x$ and $\bar x' = (x'_1, \dots, x'_k)$. Let $f(\bar x, \bar x')$ and $g(\bar x')$ be switching functions represented by binary decision diagrams $t_f$ and $t_g$ that are ordered with respect to it. The *relational product* of $t_f$ and $t_g$ over $\bar x'$ is the diagram

$$
\exists x'_1 \cdots \exists x'_k.\ \mathrm{apply}(\wedge, t_f, t_g),
$$

where each $\exists x'_i$ is the [existential quantification](exists-var.md) of a diagram over one variable.

**Theorem.**
1. The relational product evaluates, under every assignment to $\bar x$, to $\exists \bar x'.\, (f(\bar x, \bar x') \wedge g(\bar x'))$. As a function of $\bar x$, this is $1$ exactly when some assignment to $\bar x'$ makes both $f$ and $g$ true.
2. If $t_f$ and $t_g$ are reduced ordered BDDs, so is their relational product. It is therefore the unique ROBDD of that function.

**Proof.**
1. [Apply](../reduced-ordered-binary-decision-diagrams-canonic/eval-apply.md) evaluates to the conjunction. Each single-variable quantification evaluates to the disjunction of the two cofactors, which is $\exists x'_i$ of the function. Induction over the $k$ quantified variables gives part 1.
2. Apply preserves orderedness and reducedness, and so does [single-variable quantification](is-robdd-exists-var.md). Uniqueness follows from canonicity of ROBDDs.

In symbolic model checking, $f$ is the transition relation $\Delta(\bar x, \bar x')$ and $g$ is a state set renamed to the primed variables. The relational product is then the set of states with a successor in the set.

## Depends on

- [Existential quantification of a BDD over a variable](exists-var.md)

## Proof depends on

- [Evaluation of apply](../reduced-ordered-binary-decision-diagrams-canonic/eval-apply.md)
- [Quantification preserves ROBDDs](is-robdd-exists-var.md)

## Sources

- J.-P. Katoen, *Model Checking*, Lecture 18 "Reduced Ordered Binary Decision Diagrams", RWTH Aachen University, 2019/20, <https://moves.rwth-aachen.de/wp-content/uploads/WS1920/MC/mc2019_handout_lec18.pdf>: logical operations and quantification on switching functions, with $\exists z. f = f|_{z=0} \vee f|_{z=1}$, and the canonicity of ROBDDs (one node per consistent cofactor).
- J.-P. Katoen, *Model Checking*, Lecture 19 "Symbolic Model Checking with BDDs", RWTH Aachen University, 2019/20, <https://moves.rwth-aachen.de/wp-content/uploads/WS1920/MC/mc2019_handout_lec19.pdf>: the symbolic image $\exists \bar x'.\, (\Delta(\bar x, \bar x') \wedge f_j(\bar x'))$, where $f_j(\bar x')$ arises from $f_j$ by renaming $x_i$ into $x'_i$ (slide 21). The composition argument is written out here.
