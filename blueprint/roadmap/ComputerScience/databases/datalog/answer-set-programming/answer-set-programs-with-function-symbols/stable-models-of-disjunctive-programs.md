# Stable models of disjunctive programs with function symbols

A disjunctive logic program with function symbols is grounded over its Herbrand universe, possibly into infinitely many ground rules; a stable model is a Herbrand interpretation that is a minimal model of the program's reduct with respect to that interpretation.

**Programs.** A *disjunctive rule* has the form $A_1 \vee \dots \vee A_m \leftarrow L_1, \dots, L_n$ with $m > 0$ and $n \ge 0$, where each $A_j$ is an atom and each $L_i$ is a literal, either an atom $A$ or a negated atom $\mathit{not}\, A$; atoms are built from predicates and terms, and terms from variables, constants and function symbols. For a rule $r$ let $\mathrm{head}(r) = \{A_1, \dots, A_m\}$, and let $\mathrm{body}^+(r)$ and $\mathrm{body}^-(r)$ be the sets of atoms $A$ such that $A$, respectively $\mathit{not}\, A$, occurs among the $L_i$. A *disjunctive program* is a finite set of disjunctive rules, and it is *normal* if every rule has exactly one head atom. Its *ground instantiation* $\mathrm{Ground}(P)$ is the set of all instances of its rules obtained by substituting ground terms over the constants and function symbols of $P$ for the variables; it is countable and, when $P$ has a function symbol, may be infinite.

**Stable models.** A *Herbrand interpretation* is a set $M$ of ground atoms. It satisfies a ground rule $r$ without negated atoms if $\mathrm{head}(r) \cap M \ne \emptyset$ whenever $\mathrm{body}^+(r) \subseteq M$, and it is a *minimal model* of a set of such rules if it satisfies all of them and no proper subset does. The *Gelfond–Lifschitz reduct* $P^M$ is obtained from $\mathrm{Ground}(P)$ by removing every rule $r$ with $\mathrm{body}^-(r) \cap M \ne \emptyset$ and deleting the negated atoms from the remaining rules. $M$ is a *stable model* of $P$ if $M$ is a minimal model of $P^M$.

**Consequences.** $P$ is *consistent* if it has a stable model and *inconsistent* otherwise. A closed first-order formula is a *skeptical consequence* of $P$ if every stable model of $P$ satisfies it, and a *credulous consequence* if some stable model does.

A program may have no, one or several stable models, and stable models may be infinite. For a normal program the reduct $P^M$ has a least model, and $M$ is stable exactly when it equals that least model; for normal programs these are the [answer sets](answer-sets-of-normal-programs.md) in the stable model semantics of Gelfond and Lifschitz.

## Depends on

None.

## Proof depends on

None.

## Sources

- Sabrina Baselice, Piero A. Bonatti and Giovanni Criscuolo, "On finitely recursive programs", Theory and Practice of Logic Programming 9(2), pp. 213–238, 2009, <https://doi.org/10.1017/S147106840900372X>; Section 2 ("Preliminaries") of arXiv:0901.2850v1, the version read, <https://arxiv.org/abs/0901.2850v1>.
