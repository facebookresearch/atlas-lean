# Adaptation completeness of the frame rule

From a specification statement $\{p\} - \{q\}$ with modifiable variables $X$, the frame rule and the rule of consequence derive every statement that holds of all local predicate transformers satisfying $\{p\} - \{q\}$. The least such transformer sends $r$ to $p \ast \forall X.\,(q \mathrel{-\!\!\ast} r)$.

Fix a set $X$ of variables and work with the predicates, $\ast$, $\forall X$ and $X \#$ of [local predicate transformers](local-predicate-transformers.md). For predicates $q, r$ let

$$q \mathrel{-\!\!\ast} r = \{(s, h) : \text{for all } h' \text{ with } h' \# h \text{ and } (s, h') \in q,\ (s, h \ast h') \in r\}.$$

A *specification statement* $\{p\} - \{q\}$ is a pre/postcondition pair with no command. $\{p\} - \{q\} \vdash_X \{p'\} - \{q'\}$ holds if $\{p'\} - \{q'\}$ is derivable from $\{p\} - \{q\}$ by *consequence*, from $\{p\} - \{q\}$ with $p' \subseteq p$ and $q \subseteq q'$ infer $\{p'\} - \{q'\}$, and the *frame rule*, from $\{p\} - \{q\}$ with $X \# r$ infer $\{p \ast r\} - \{q \ast r\}$. Semantically, $t \models_X \{p\} - \{q\}$ means $p \subseteq t(q)$ for $t \in \mathrm{LPT}(X)$, and $\{p\} - \{q\} \models_X \{p'\} - \{q'\}$ means that every $t \in \mathrm{LPT}(X)$ with $t \models_X \{p\} - \{q\}$ satisfies $t \models_X \{p'\} - \{q'\}$.

1. The transformer $t = \lambda r.\ p \ast \forall X.\,(q \mathrel{-\!\!\ast} r)$ lies in $\mathrm{LPT}(X)$, satisfies $p \subseteq t(q)$, and is the least such element of $\mathrm{LPT}(X)$ in the pointwise order.
2. $\{p\} - \{q\} \vdash_X \{p'\} - \{q'\}$ if and only if $\{p\} - \{q\} \models_X \{p'\} - \{q'\}$.

## Depends on

- [Local predicate transformers](local-predicate-transformers.md)
- [Separating implication](../separating-implication-and-small-axioms/separating-implication.md)

## Proof depends on

- [Local predicate transformers](local-predicate-transformers.md)
- [Adjunction between separating conjunction and separating implication](../separating-implication-and-small-axioms/adjunction-between-separating-conjunction-and-implication.md)

## Expansion

Soundness holds because transformers are monotone and local. For part 1, monotonicity is clear; locality follows from $\forall X.\,(q \mathrel{-\!\!\ast} r) \ast r' \subseteq \forall X.\,(q \mathrel{-\!\!\ast} (r \ast r'))$ when $X \# r'$; $p \subseteq t(q)$ because $\mathrm{emp} \subseteq \forall X.\,(q \mathrel{-\!\!\ast} q)$; and any local $t'$ with $p \subseteq t'(q)$ satisfies $t'(r) \supseteq t'(q \ast \forall X.\,(q \mathrel{-\!\!\ast} r)) \supseteq t'(q) \ast \forall X.\,(q \mathrel{-\!\!\ast} r) \supseteq t(r)$, using $q \ast \forall X.\,(q \mathrel{-\!\!\ast} r) \subseteq r$, which is $\forall$-elimination with modus ponens for $\ast$ and $\mathrel{-\!\!\ast}$. For completeness, a semantic consequence gives $p' \subseteq t(q')$ by minimality of $t$; framing $\{p\} - \{q\}$ with $\forall X.\,(q \mathrel{-\!\!\ast} q')$, which is independent of $X$, and one consequence step derive $\{p'\} - \{q'\}$. So every consequence needs at most one use of each rule. The result is concrete, for stores and heaps with a modifies set; it differs from the completeness of abstract separation logic for local actions, which concerns derivations from axioms for primitive commands.

## Sources

- H. Yang and P. O'Hearn, "A semantic basis for local reasoning", *Foundations of Software Science and Computation Structures (FoSSaCS 2002)*, LNCS 2303, Springer, 2002, pp. 402–416, <https://doi.org/10.1007/3-540-45931-6_28>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf>, Section 5, Table 3 and the definition of specification statements; Section 5.3, the definitions of $\vdash_X$ and $\models_X$, Proposition 3, Theorem 2, Lemma 3 and the proof of Theorem 2.
