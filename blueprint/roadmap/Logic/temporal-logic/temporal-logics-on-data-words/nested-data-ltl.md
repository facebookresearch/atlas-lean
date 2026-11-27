# Nested data LTL

Nested data LTL (ND-LTL) is a temporal logic for words whose positions carry the values of several attributes ordered as a forest; besides LTL navigation along all positions, it navigates along the positions that share the current value of an attribute together with the values of all attributes below it.

**Definition.** Let $AP$ be a finite set of propositions, $\Delta$ an infinite set of data values and $A$ a finite set of attributes carrying a *tree order* $\le$, a partial order in which the downward closure $x{\downarrow}$ of every attribute is a chain. A *multi-attributed data word* is a finite or infinite sequence $w = (a_0, d_0)(a_1, d_1)\cdots$ with $a_i \subseteq AP$ and $d_i : A \to \Delta$. Position formulae $\varphi$ and class formulae $\psi$ are

$$
\varphi ::= p \mid \varphi \wedge \varphi \mid \neg\varphi \mid \mathsf X\varphi \mid \mathsf Y\varphi \mid \varphi\,\mathsf U\,\varphi \mid \varphi\,\mathsf S\,\varphi \mid \mathsf C^r_x\psi, \qquad \psi ::= @x \mid \psi \wedge \psi \mid \neg\psi \mid \mathsf X^{=}\psi \mid \mathsf Y^{=}\psi \mid \psi\,\mathsf U^{=}\psi \mid \psi\,\mathsf S^{=}\psi \mid \varphi,
$$

with $p \in AP$, $x \in A$ and $r \in \mathbb Z$. For $x$ with $x{\downarrow} = \{x_1 < \cdots < x_n\}$, a map $d$ on $x{\downarrow}$ determines the vector $(d(x_1), \ldots, d(x_n))$, and $d \simeq d'$ means equal vectors. Let $\mathrm{pos}_d(w)$ be the set of positions $i$ such that $d \simeq d_i|_{y{\downarrow}}$ for some $y \in A$. Position formulae are evaluated at positions $(w, i)$ with LTL semantics for the Boolean and LTL operators, and $(w, i) \models \mathsf C^r_x\psi$ iff $0 \le i + r < |w|$ and $(w, i + r, d_i|_{x{\downarrow}}) \models \psi$. Class formulae are evaluated at $(w, i, d)$: $@x$ holds iff $d_i|_{x{\downarrow}} \simeq d$; $\mathsf X^{=}\psi$ holds iff $\psi$ holds at the least $j > i$ in $\mathrm{pos}_d(w)$; $\psi_1\,\mathsf U^{=}\psi_2$ holds iff some $j \ge i$ in $\mathrm{pos}_d(w)$ satisfies $\psi_2$ and every $j' \in \mathrm{pos}_d(w)$ with $i \le j' < j$ satisfies $\psi_1$; $\mathsf Y^{=}$ and $\mathsf S^{=}$ are the past versions; and a position formula $\varphi$ holds iff $(w, i) \models \varphi$. The fragment *ND-LTL$^-$* omits $\mathsf X^{=}$ and $\mathsf U^{=}$, and *ND-LTL$^+$* omits $\mathsf Y^{=}$ and $\mathsf S^{=}$. Satisfiability asks whether $w \models \varphi$, that is $(w, 0) \models \varphi$, for some data word $w$.

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)
- [Partially ordered set](../../../Order/ordered-sets/partial-order.md)

## Proof depends on

None.

## Expansion

With a single attribute, or attributes ordered trivially, ND-LTL is the logic BD-LTL of Kara, Schwentick and Zeume, whose satisfiability is decidable but as hard as Petri net reachability. Satisfiability of BD-LTL$^+$ and BD-LTL$^-$ is 2EXPSPACE-complete over finite and infinite data words (Theorem 3 of the source). The tree order lets a class quantifier bind a tuple of values, such as a list, an iterator of it and a state of the list, while keeping decidability for some fragments.

## Sources

- N. Decker, P. Habermehl, M. Leucker and D. Thoma, "Ordered Navigation on Multi-attributed Data Words", in *CONCUR 2014 – Concurrency Theory*, Lecture Notes in Computer Science 8704, Springer, 2014, pp. 497–511, <https://doi.org/10.1007/978-3-662-44584-6_34>; read as arXiv:1404.6064v1, <https://arxiv.org/abs/1404.6064v1>: Section 2 (data words, tree orders), Section 3 (syntax and semantics of BD-LTL, Definition 1), Section 4 (Theorem 3), Section 5 (Definition 3 and the semantics of ND-LTL).
