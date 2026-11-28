# Hereditarily undecidable theories of classes of structures

The theory of a class of structures is hereditarily undecidable when every theory that interprets it, in the sense of uniform interpretability with parameters, is undecidable; for a single theory the notion asks that every set of sentences between the valid ones and the theory be undecidable.

**Theories of classes.** For a class $\mathcal{K}$ of structures in a finite language, $\mathrm{Th}(\mathcal{K})$ is the set of first-order sentences true in every member of $\mathcal{K}$, and $\mathcal{K}_{\mathrm{fin}}$ is the class of finite members of $\mathcal{K}$.

**Interpretability ordering (Willard).** For theories $T_1, T_2$ in possibly different finite languages, $T_1 \leq T_2$ means that there is $\mathcal{K}_1 \subseteq \mathrm{Mod}(T_1)$ with $\mathrm{Th}(\mathcal{K}_1) = T_1$ whose members are uniformly interpretable by formulas, with parameters and definable factor relations, in the models of $T_2$. A theory $T_1$ is *hereditarily undecidable* in this sense if every theory $T_2$ with $T_1 \leq T_2$ is undecidable.

**Hereditary undecidability of a set of sentences (Nies).** For a language $L$, let $L\text{-Valid}$ be the set of $L$-sentences true in all $L$-structures. A set $U$ of $L$-sentences is *hereditarily undecidable* if every set $X$ with $L\text{-Valid} \cap U \subseteq X \subseteq U$ is undecidable. A formula is $\Sigma_k$ (respectively $\Pi_k$) if it consists of $k$ alternating blocks of quantifiers starting with $\exists$ (respectively $\forall$) followed by a quantifier-free formula, and $\Sigma_k\text{-}\mathrm{Th}(\mathcal{C})$ and $\Pi_k\text{-}\mathrm{Th}(\mathcal{C})$ are the sets of $\Sigma_k$ and $\Pi_k$ sentences of $\mathrm{Th}(\mathcal{C})$.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Both notions make undecidability transferable: Willard's ordering is a variant of Rabin's method of interpretations, and the ordering has a maximum element, the theory of all graphs; Nies's notion is tailored to fragments, so that undecidability of a fragment of one class transfers to a fragment of another along definability schemes that count quantifier alternations.

## Sources

- R. Willard, "Hereditary undecidability of some theories of finite structures", *Journal of Symbolic Logic* 59(4):1254–1262, 1994, doi:10.2307/2275703; read in the author's open-access copy at <https://math.uwaterloo.ca/~rdwillar/documents/Publications/graphs.pdf>: Section 1 (the ordering $\leq$ and the definition of hereditary undecidability).
- A. Nies, "Undecidable fragments of elementary theories", *Algebra Universalis* 35(1):8–33, 1996, doi:10.1007/BF01190967; read in the author's open-access copy at <https://www.cs.auckland.ac.nz/~nies/papers/Fragments.pdf>: Section 1 (the definition of hereditary undecidability of a set of sentences, $\Sigma_k$ and $\Pi_k$ formulas) and the conventions before Section 2.
