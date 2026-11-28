# HyperQPTL

HyperQPTL extends HyperLTL with quantification over atomic propositions, as QPTL extends LTL: besides trace quantifiers $\forall\pi$, $\exists\pi$ it has propositional quantifiers $\forall q$, $\exists q$ that choose one $q$-sequence shared by all traces, which makes $\omega$-regular hyperproperties expressible.

**Syntax.** For a set $\mathrm{AP}$ of atomic propositions and trace variables $\pi$:

$$
\varphi ::= \forall\pi.\varphi \mid \exists\pi.\varphi \mid \forall q.\varphi \mid \exists q.\varphi \mid \psi, \qquad \psi ::= a_\pi \mid q \mid \neg\psi \mid \psi \vee \psi \mid X\psi \mid F\psi,
$$

with $a, q \in \mathrm{AP}$; each $a_\pi$ must lie in the scope of a quantifier binding $\pi$ and each $q$ in the scope of a quantifier binding $q$, and variable names are not reused. Until is definable with propositional quantification.

**Semantics.** For a set $T \subseteq (2^{\mathrm{AP}})^\omega$ of traces, an assignment $\Pi$ of traces of $T$ to trace variables and a position $i$: $\Pi, i \models_T a_\pi$ iff $a \in \Pi(\pi)[i]$; $\Pi, i \models_T q$ iff $q \in t[i]$ for all $t \in T$; Booleans, $X$ and $F$ are as in LTL; $\exists\pi$ and $\forall\pi$ range over $t \in T$; and

$$
\Pi, i \models_T \exists q.\varphi \iff \exists t_q \in (2^{\{q\}})^\omega.\ \Pi, i \models_{T[q \mapsto t_q]} \varphi,
$$

where $T[q \mapsto t_q]$ replaces the $q$-component of every trace of $T$ by $t_q$, so that in the scope of the quantifier all traces agree on $q$ (and dually for $\forall q$). $T$ satisfies a closed formula $\varphi$ if $\varnothing, 0 \models_T \varphi$.

HyperLTL is the fragment without propositional quantifiers, and QPTL embeds into HyperQPTL with a single universal trace quantifier. Fragments are named by their quantifier prefixes: for example the $\forall\exists$ fragment consists of the formulas whose trace quantifiers form one universal followed by one existential quantifier, and $\forall_q^*\exists_q^*\forall_\pi$ formulas have a block of universal propositional quantifiers, then existential propositional quantifiers, then a single universal trace quantifier.

## Depends on

- [HyperLTL](../hyperltl.md)

## Proof depends on

None.

## Expansion

HyperQPTL is strictly more expressive than HyperLTL and than first-order logic with the equal-level predicate, and strictly less expressive than S1S with the equal-level predicate; it can express promptness and epistemic properties. Its model-checking problem over finite Kripke structures is decidable.

## Sources

- B. Finkbeiner, C. Hahn, J. Hofmann and L. Tentrup, "Realizing ω-regular hyperproperties", in *Computer Aided Verification (CAV 2020)*, Lecture Notes in Computer Science 12225, Springer, 2020, pp. 40–63, doi:10.1007/978-3-030-53291-8_4; read as arXiv:2101.07161v1, <https://arxiv.org/abs/2101.07161v1>: Section 3 (syntax and semantics of HyperQPTL).
- N. Coenen, B. Finkbeiner, C. Hahn and J. Hofmann, "The hierarchy of hyperlogics", in *34th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2019)*, IEEE, 2019, pp. 1–13, doi:10.1109/LICS.2019.8785713; read as arXiv:2005.05934v1, <https://arxiv.org/abs/2005.05934v1>: Section 3 (HyperQPTL and its place in the expressiveness hierarchy).
