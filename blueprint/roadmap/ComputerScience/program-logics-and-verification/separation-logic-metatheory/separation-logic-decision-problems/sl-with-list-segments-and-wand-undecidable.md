# Satisfiability of quantifier-free separation logic with list segments and magic wand is undecidable

Quantifier-free separation logic with separating conjunction, separating implication (magic wand) and the list segment predicate has an undecidable satisfiability problem, and its valid formulas are not recursively enumerable. Dropping the magic wand gives PSPACE-complete fragments, even with a reachability predicate.

**Setting (Demri, Lozes and Mansutti).** Fix a countably infinite set of program variables and of locations. A *memory state* is a pair $(s, h)$ of a store $s$ mapping variables to locations and a heap $h$, a partial function from locations to locations with finite domain (one record field). Formulas of $\mathrm{SL}(\ast, -\!\!\ast, \mathtt{ls})$ are

$$
\pi ::= \mathtt{emp} \mid x = y \mid x \hookrightarrow y \mid \mathtt{ls}(x, y), \qquad \varphi ::= \pi \mid \neg\varphi \mid \varphi \wedge \varphi \mid \varphi \ast \varphi \mid \varphi \mathrel{-\!\!\ast} \varphi,
$$

with $(s, h) \models \mathtt{emp}$ iff $h$ is empty; $x = y$ iff $s(x) = s(y)$; $x \hookrightarrow y$ iff $s(x) \in \mathrm{dom}(h)$ and $h(s(x)) = s(y)$; $\mathtt{ls}(x, y)$ iff either $h$ is empty and $s(x) = s(y)$, or $h = \{\ell_0 \mapsto \ell_1, \dots, \ell_{n-1} \mapsto \ell_n\}$ for some $n \ge 1$ with pairwise distinct $\ell_0, \dots, \ell_n$, $\ell_0 = s(x)$ and $\ell_n = s(y)$; $\varphi_1 \ast \varphi_2$ iff $h$ splits into disjoint $h_1 + h_2$ with $(s, h_i) \models \varphi_i$; and $\varphi_1 \mathrel{-\!\!\ast} \varphi_2$ iff for every heap $h'$ disjoint from $h$ with $(s, h') \models \varphi_1$, $(s, h + h') \models \varphi_2$. A formula is *satisfiable* if some memory state satisfies it.

**Theorem (Demri, Lozes and Mansutti).** The satisfiability problem for $\mathrm{SL}(\ast, -\!\!\ast, \mathtt{ls})$ is undecidable, and the set of valid $\mathrm{SL}(\ast, -\!\!\ast, \mathtt{ls})$ formulas is not recursively enumerable.

The paper also notes that the set of satisfiable formulas is not recursively enumerable either, and derives undecidability for $\mathrm{SL}(\ast, -\!\!\ast)$ extended with atoms expressing $\mathtt{reach}(x, y) = 2$ and $\mathtt{reach}(x, y) = 3$. In contrast, it shows that $\mathrm{SL}(\ast, \mathtt{reach}^+)$ and variants are PSPACE-complete.

## Depends on
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

The proof translates first-order separation logic with the magic wand and one record field, $\mathrm{SL}(\forall, -\!\!\ast)$, into $\mathrm{SL}(\ast, -\!\!\ast, \mathtt{ls})$ so that satisfiability and validity are preserved; $\mathrm{SL}(\forall, -\!\!\ast)$ has an undecidable satisfiability problem and a non-r.e. set of valid formulas (Brochenin, Demri and Lozes; Demri and Deters). The key is that $\mathtt{ls}$ together with $\ast$ and $-\!\!\ast$ can express, for program variables $x, y$, properties of the locations reached in one step (such as $n(x) = n(y)$, $n(x) \hookrightarrow n(y)$ and "some cell points to $x$"), which lets quantified variables be simulated by heap cells.

A good expansion links the undecidability of satisfiability and the non-recursive-enumerability of validity for $\mathrm{SL}(\forall, -\!\!\ast)$ (Brochenin, Demri and Lozes).

## Sources

- Stéphane Demri, Étienne Lozes and Alessio Mansutti, "The Effects of Adding Reachability Predicates in Quantifier-Free Separation Logic", ACM Transactions on Computational Logic 22(2):1–56, 2021, <https://doi.org/10.1145/3448269>; read in arXiv:1810.05410v2, <https://arxiv.org/abs/1810.05410v2>: Section 2.1 (syntax and semantics), Proposition 3.1, Theorems 3.12 (undecidability) and 3.13 (validities not r.e.) with the remarks that follow them, Corollary 3.15 ($\mathtt{reach}(x, y) = 2$ and $= 3$) and Corollary 3.16 (further undecidable variants) in Section 3.5, in the numbering of that version.
- Rémi Brochenin, Stéphane Demri and Étienne Lozes, "On the almighty wand", Information and Computation 211, pp. 106–137, 2012, <https://doi.org/10.1016/j.ic.2011.12.003>; undecidability of $\mathrm{SL}(\forall, -\!\!\ast)$; cited for attribution, the result as read in Section 3 of the paper by Stéphane Demri, Étienne Lozes and Alessio Mansutti above (arXiv:1810.05410v2).
