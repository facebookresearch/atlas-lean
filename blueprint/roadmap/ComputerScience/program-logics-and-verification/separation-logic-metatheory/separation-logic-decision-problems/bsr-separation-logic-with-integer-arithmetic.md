# Bernays–Schönfinkel–Ramsey separation logic with integer arithmetic is undecidable

Separation logic describes heaps with a separating conjunction and its adjoint, the magic wand. In its Bernays–Schönfinkel–Ramsey fragment, sentences with an $\exists^*\forall^*$ prefix over a quantifier-free matrix, satisfiability becomes undecidable once heap locations are integers with linear arithmetic.

**Setting (Reynolds, Iosif and Serban).** Fix a theory $T$ and two of its sorts, $\mathsf{Loc}$ (interpreted as a countable set, with a constant $\mathsf{nil}$) and $\mathsf{Data}$. Given an interpretation $\mathcal{I}$ of $T$, a *heap* is a finite partial map $h$ from $\mathsf{Loc}^{\mathcal{I}}$ to $\mathsf{Data}^{\mathcal{I}}$. Formulas of $\mathsf{SL}(T)_{\mathsf{Loc},\mathsf{Data}}$ extend first-order formulas of $T$ with $\mathsf{emp}$ (the heap is empty), points-to atoms $t \mapsto u$ (the heap is the single cell mapping $t \ne \mathsf{nil}$ to $u$), the separating conjunction $\varphi_1 * \varphi_2$ (the heap splits into two disjoint parts satisfying $\varphi_1$ and $\varphi_2$), and the magic wand $\varphi_1 \mathrel{-\!\!*} \varphi_2$ (every disjoint extension satisfying $\varphi_1$ yields a heap satisfying $\varphi_2$). A formula is satisfiable if some interpretation of $T$ and heap satisfy it. $\exists^*\forall^*\mathsf{SL}(T)_{\mathsf{Loc},\mathsf{Data}}$ consists of the sentences $\exists x_1 \dots \exists x_m \forall y_1 \dots \forall y_n\, \varphi$ with $\varphi$ quantifier-free. $\mathsf{LIA}$ is linear integer arithmetic over the sort $\mathbb{Z}$, $\mathsf{E}$ the empty theory with equality, whose signature has a sort $U$ and no function symbols, and $\mathsf{ELIA}$ the extension of $\mathsf{LIA}$ by the sort $U$ of $\mathsf{E}$ with equality over it.

**Theorem (Reynolds, Iosif and Serban).** The satisfiability problems for

$$
\exists^*\forall^*\mathsf{SL}(\mathsf{LIA})_{\mathbb{Z},\mathbb{Z}}
\qquad\text{and}\qquad
\exists^*\forall^*\mathsf{SL}(\mathsf{ELIA})_{U,\, U \times \mathbb{Z}}
$$

are undecidable.

The same paper claimed $\exists^*\forall^*\mathsf{SL}(\mathsf{E})_{U,U^k}$ to be PSPACE-complete; Echenim, Iosif and Peltier later corrected this claim and showed that fragment undecidable for $k \ge 2$ ([satisfiability of Bernays–Schönfinkel–Ramsey separation logic](satisfiability-of-bsr-separation-logic.md)).

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof reduces Hilbert's tenth problem over $\mathbb{N}$. A Diophantine equation is first rewritten as an equisatisfiable system of linear equations and equations $x = y^2$, replacing each product $x = yz$ through $2x + y^2 + z^2 = (y + z)^2$. With integer locations, a heap is made to allocate exactly a finite initial segment of the perfect squares: $\exists^*\forall^*$ constraints force allocated cells to form an acyclic list with strictly increasing addresses whose consecutive gaps grow by $2$. Then $x = y^2$ becomes "$x$ and $x + 2y + 1$ are allocated and nothing in between is", which is again in the fragment. A good expansion links a page for the analogous undecidability of the $\exists^*\forall^* \cap \forall^*\exists^*$ fragment of Presburger arithmetic with one monadic predicate interpreted over finite sets, the lemma the reduction refines.

## Sources

- Andrew Reynolds, Radu Iosif and Cristina Serban, *Reasoning in the Bernays-Schönfinkel-Ramsey Fragment of Separation Logic*, Verification, Model Checking, and Abstract Interpretation (VMCAI 2017), Lecture Notes in Computer Science 10145, Springer, 2017, pp. 462–482, https://doi.org/10.1007/978-3-319-52234-0_25; the section on integer locations with linear arithmetic (the undecidability theorems for $\mathsf{SL}(\mathsf{LIA})_{\mathbb{Z},\mathbb{Z}}$ and $\exists^*\forall^*\mathsf{SL}(\mathsf{ELIA})_{U,U \times \mathbb{Z}}$, Theorem 5), read in arXiv:1610.04707v2.
- Mnacho Echenim, Radu Iosif and Nicolas Peltier, *The Bernays-Schönfinkel-Ramsey Class of Separation Logic on Arbitrary Domains*, FoSSaCS 2019, Lecture Notes in Computer Science 11425, Springer, 2019, pp. 242–259, https://doi.org/10.1007/978-3-030-17127-8_14, for the correction of the PSPACE claim, read in arXiv:1802.00195v2.
