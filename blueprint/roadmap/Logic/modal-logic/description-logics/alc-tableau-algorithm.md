# Tableau algorithm for ALC

Use the concepts, interpretations and ABoxes of [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md). A concept is in *negation normal form* if negation occurs only directly in front of concept names; every ALC concept can be transformed in linear time into an equivalent one in negation normal form. Let $C_0$ be an ALC concept in negation normal form. The algorithm works on finite sets of ABoxes, starting from $\{\{C_0(x_0)\}\}$; a rule takes one ABox $\mathcal A$ of the set and replaces it by one or two ABoxes:

- **$\to_\sqcap$:** if $(C_1 \sqcap C_2)(x) \in \mathcal A$ but not both $C_1(x)$ and $C_2(x)$, replace $\mathcal A$ by $\mathcal A \cup \{C_1(x), C_2(x)\}$;
- **$\to_\sqcup$:** if $(C_1 \sqcup C_2)(x) \in \mathcal A$ but neither $C_1(x)$ nor $C_2(x)$, replace $\mathcal A$ by the two ABoxes $\mathcal A \cup \{C_1(x)\}$ and $\mathcal A \cup \{C_2(x)\}$;
- **$\to_\exists$:** if $(\exists r.C)(x) \in \mathcal A$ but there is no individual $z$ with $C(z)$ and $r(x, z)$ in $\mathcal A$, replace $\mathcal A$ by $\mathcal A \cup \{C(y), r(x, y)\}$ for an individual name $y$ not occurring in $\mathcal A$;
- **$\to_\forall$:** if $(\forall r.C)(x)$ and $r(x, y)$ are in $\mathcal A$ but $C(y)$ is not, replace $\mathcal A$ by $\mathcal A \cup \{C(y)\}$.

A finite set of ABoxes is consistent if one of its members is. An ABox is *complete* if no rule applies to it, contains a *clash* if $\{P(x), \neg P(x)\} \subseteq \mathcal A$ for some individual $x$ and concept name $P$, and is *closed* if it contains a clash and *open* otherwise. Here $\top$ and $\bot$ are read as abbreviations of $P \sqcup \neg P$ and $P \sqcap \neg P$ for a concept name $P$. The algorithm applies rules in arbitrary order until none applies and answers "satisfiable" if the resulting set contains an open ABox, "unsatisfiable" otherwise. Started from a single ABox in negation normal form instead of $\{C_0(x_0)\}$, the same rules test ABox consistency.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)

## Sources

- F. Baader and U. Sattler, "An overview of tableau algorithms for description logics", *Studia Logica* 69(1):5–40, 2001, <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSattler-StudiaLogica.pdf>, Section 3, negation normal form, Figure 1 (transformation rules), Definition 3 and the description of the algorithm, pp. 7–8 (after M. Schmidt-Schauß and G. Smolka, 1991), and Section 3.2, the algorithm for ABox consistency, p. 10.
