# Freeze LTL with quasi-ordered attributes

Freeze LTL with quasi-ordered attributes is a temporal logic on finite data words whose positions carry a letter and a data value for each attribute. A freeze quantifier $\downarrow^x$ stores the values of $x$ and of every attribute below it, and a check $\uparrow^x$ compares them with the current position.

**Data words.** Fix a finite alphabet $\Sigma$, an infinite data domain $\Delta$, and a finite set $A$ of attributes with a quasi-ordering $\sqsubseteq$ (reflexive and transitive). An *$A$-attributed data word* is a nonempty finite word $w = (a_1, \mathbf{d}_1) \cdots (a_n, \mathbf{d}_n) \in (\Sigma \times \Delta^A)^+$. For $x \in A$ let $\mathrm{cl}(x) = \{y \in A : y \sqsubseteq x\}$, let $\mathbf{d}|_x$ be the restriction of $\mathbf{d}$ to $\mathrm{cl}(x)$, and let $\Delta^A_\bot$ be the set of these partial valuations. Two partial valuations $\mathbf{d}, \mathbf{d}'$ are *equivalent*, $\mathbf{d} \simeq \mathbf{d}'$, if some bijection $h : \mathrm{dom}(\mathbf{d}) \to \mathrm{dom}(\mathbf{d}')$ preserves and reflects $\sqsubseteq$ and satisfies $\mathbf{d}(y) = \mathbf{d}'(h(y))$.

**Syntax and semantics.** Formulas of $\mathrm{LTL}^{\downarrow}_A$ are $\varphi ::= a \mid \neg\varphi \mid \varphi \wedge \varphi \mid X\varphi \mid \varphi \mathbin{U} \varphi \mid {\downarrow^x}\varphi \mid {\uparrow^x}$ with $a \in \Sigma$ and $x \in A$. For a position $i$ of $w$ and a stored partial valuation $\mathbf{d} \in \Delta^A_\bot$: $(w, i, \mathbf{d}) \models a$ iff $a_i = a$; Boolean connectives are as usual; $(w, i, \mathbf{d}) \models X\varphi$ iff $i < n$ and $(w, i+1, \mathbf{d}) \models \varphi$; $(w, i, \mathbf{d}) \models \varphi \mathbin{U} \psi$ iff for some $k$ with $i \leq k \leq n$, $(w, k, \mathbf{d}) \models \psi$ and $(w, j, \mathbf{d}) \models \varphi$ for all $i \leq j < k$;

$$
(w, i, \mathbf{d}) \models {\downarrow^x}\varphi \iff (w, i, \mathbf{d}_i|_x) \models \varphi, \qquad (w, i, \mathbf{d}) \models {\uparrow^x} \iff \mathbf{d}|_y \simeq \mathbf{d}_i|_x \text{ for some } y \in A.
$$

For sentences, in which every check lies under a freeze quantifier, $w \models \varphi$ means $(w, 1, \mathbf{d}) \models \varphi$ for any $\mathbf{d}$. The *satisfiability problem* asks whether some $A$-attributed data word satisfies a given sentence.

**Tree-quasi-orderings.** $(A, \sqsubseteq)$ is a *tree-quasi-ordering* if for every $x \in A$ the downward closure $\mathrm{cl}(x)$ is totally quasi-ordered; equivalently, there are no $x, y, z$ with $x \sqsubseteq z$, $y \sqsubseteq z$ and $x$, $y$ incomparable.

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Remarks

With the identity ordering on a single attribute this is the one-register freeze LTL of Demri and Lazić. For a linear ordering $[k] = \{1 < \dots < k\}$, freezing attribute $x$ stores the prefix $d_1 \dots d_x$ of the value vector and a check succeeds if the current prefix of length $y$ agrees with a stored one. If $x \sqsubseteq z \sqsupseteq y$ with $x$, $y$ incomparable, freezing $z$ stores the *set* of values of $x$ and $y$, which is what makes undecidability possible.

## Sources

- N. Decker and D. Thoma, "On freeze LTL with ordered attributes", in *Foundations of Software Science and Computation Structures (FoSSaCS 2016)*, Lecture Notes in Computer Science 9634, Springer, 2016, pp. 269–284, doi:10.1007/978-3-662-49630-5_16; read as arXiv:1504.06355v2 (extended version), <https://arxiv.org/abs/1504.06355v2>: the section "Semantics and Undecidability of LTL↓qo" (attributed data words, restrictions to downward closures, the equivalence of partial valuations, the semantics, and tree-quasi-orderings).
