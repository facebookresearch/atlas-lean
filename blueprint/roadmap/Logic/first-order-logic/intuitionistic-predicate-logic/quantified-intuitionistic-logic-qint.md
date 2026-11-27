# Quantified intuitionistic logic $\mathbf{QInt}$

$\mathbf{QInt}$ is the set of first-order formulas, over $\bot, \top, \wedge, \vee, \to, \exists, \forall$, that are true in every intuitionistic Kripke model: a partial order of worlds with expanding domains and monotone interpretations of the predicate letters.

**Language.** Countably many individual variables, countably many predicate letters of every arity, the constants $\bot$ and $\top$, the connectives $\wedge$, $\vee$, $\to$ and the quantifiers $\exists$, $\forall$; no constants, function symbols or equality. A formula is *positive* when it does not contain $\bot$.

**Kripke models.** A frame is $\langle W, R\rangle$ with $R$ reflexive, antisymmetric and transitive. A model $\langle W, R, D, I\rangle$ assigns to each world a nonempty domain $D(w)$ with $D(w) \subseteq D(w')$ whenever $w R w'$, and to each world and $n$-ary letter $P$ a relation $I(w, P) \subseteq D(w)^n$ with $I(w, P) \subseteq I(w', P)$ whenever $w R w'$. Under an assignment $g$:

- $\bot$ is false and $\top$ true everywhere, atoms are read off $I$, and $\wedge$, $\vee$ are pointwise;
- $w \models^g \varphi \to \psi$ iff every $w'$ with $w R w'$ and $w' \models^g \varphi$ has $w' \models^g \psi$;
- $w \models^g \exists x\,\varphi$ iff some $x$-variant $g'$ with $g'(x) \in D(w)$ has $w \models^{g'} \varphi$;
- $w \models^g \forall x\,\varphi$ iff every $w'$ with $w R w'$ and every $x$-variant $g'$ with $g'(x) \in D(w')$ have $w' \models^{g'} \varphi$.

A formula is true in a model when it is true at every world under every assignment into the local domain, and $\mathbf{QInt}$ is the set of formulas true in all frames. By [Kripke completeness](../intuitionistic-first-order-logic/kripke-soundness-and-completeness-of-iqc.md) this is the set of theorems of intuitionistic predicate logic.

## Depends on

- [Partially ordered set](../../../Order/ordered-sets/partial-order.md)

## Proof depends on

None.

## Expansion

The *positive fragment* of a logic is its set of positive members. All logics between $\mathbf{QInt}$ and $\mathbf{QKC}$, the logic of the weak law of excluded middle, have the same positive fragment, which is why results about the positive fragment transfer along that interval.

## Sources

- M. Rybakov and D. Shkatov, "Undecidability of first-order modal and intuitionistic logics with two variables and one monadic predicate letter", *Studia Logica* 107(4):695–717, 2019, doi:10.1007/s11225-018-9815-7; read as arXiv:1706.05060v5, <https://arxiv.org/abs/1706.05060v5>: Section 3.1 (syntax and Kripke semantics of $\mathbf{QInt}$, and the definition of $\mathbf{QKC}$).
