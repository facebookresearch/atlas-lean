# First-order modal logics of single Kripke frames

The first-order modal logic of a Kripke frame consists of the first-order modal formulas true at every world of every predicate model over that frame, taken with expanding domains or with a constant domain.

**Language.** Formulas are built from predicate letters of any arity (a $0$-ary letter is a proposition letter) and individual variables, without constants, function symbols or equality, by $\bot$, $\to$, $\forall$ and $\Box$; the other connectives, $\exists$ and $\Diamond$ are defined as usual.

**Frames and models.** A Kripke frame is $\langle W, R\rangle$ with $W \neq \emptyset$ and $R \subseteq W \times W$. A predicate frame with expanding domains is $\langle W, R, D\rangle$ with $D(w)$ a nonempty set for each $w \in W$ and $D(w) \subseteq D(w')$ whenever $wRw'$; it has a *constant domain* if $D(w) = D(w')$ for all $w, w'$. A model adds, for each world $w$ and $n$-ary letter $P$, a relation $I(w, P) \subseteq D(w)^n$. Under an assignment $g$, $\Box\varphi$ is true at $w$ iff $\varphi$ is true at every $w'$ with $wRw'$, and $\forall x\,\varphi$ is true at $w$ iff $\varphi$ is true at $w$ for every $x$-variant $g'$ of $g$ with $g'(x) \in D(w)$. A formula is valid on a frame if it is true at every world of every model over every predicate frame based on it, under assignments into the local domains.

**Logics.** For a frame $\langle W, R\rangle$, $\mathbf{L}(W, R)$ is the set of formulas valid on it, with expanding domains, and $\mathbf{L}_c(W, R)$ the set of formulas true in all models over predicate frames with a constant domain based on it. A formula $\varphi$ is *satisfiable* for a logic $L$ if $\neg\varphi \notin L$. For a propositional modal logic $L$, $\mathbf{Q}L$ is the least predicate modal logic containing classical predicate logic and $L$.

## Depends on

- [Quantified modal logic QL](quantified-modal-logic-ql.md)
- [Kripke model](../kripke-semantics/kripke-model.md)

## Proof depends on

None.

## Expansion

$\mathbf{L}(W, R) \subseteq \mathbf{L}_c(W, R)$. For linear frames such as $(\mathbb{Q}, \leq)$ the logic is finitely axiomatizable: $\mathbf{QS4.3} = \mathbf{L}(\mathbb{Q}, \leq)$ and $\mathbf{QK4.3.D.X} = \mathbf{L}(\mathbb{Q}, <)$ (Corsi).

## Sources

- M. Rybakov and D. Shkatov, "Algorithmic properties of first-order modal logics of linear Kripke frames in restricted languages", *Journal of Logic and Computation* 31(5):1266–1288, 2021, doi:10.1093/logcom/exab030; read as arXiv:2105.11811v1, <https://arxiv.org/abs/2105.11811v1>, whose numbering is used here: Section 2 (languages, predicate Kripke frames with expanding and constant domains, the logics $\mathbf{L}(\mathfrak{C})$ and $\mathbf{L}_c(\mathfrak{C})$) and Section 5.
