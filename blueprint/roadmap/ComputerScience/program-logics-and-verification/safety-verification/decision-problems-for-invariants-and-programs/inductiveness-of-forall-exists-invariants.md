# Checking inductiveness of universal-existential invariants is undecidable

Whether a first-order invariant with a universal-existential quantifier prefix is preserved by a transition relation written in effectively propositional logic is undecidable, both over finite structures and over all structures.

**Setting (Feldman, Padon, Immerman, Sagiv and Shoham).** Fix a vocabulary $\Sigma$ of relation and constant symbols, with no function symbols, and a primed copy $\Sigma'$ for post-states. $\forall^*\exists^*(\Sigma)$ is the class of first-order sentences over $\Sigma$ of the form $\forall \vec{x}\, \exists \vec{y}\; \alpha$ with $\alpha$ quantifier-free; $\mathrm{EPR}$ is the class of sentences of the form $\exists \vec{x}\, \forall \vec{y}\; \alpha$ over $\Sigma \uplus \Sigma'$. A sentence $I$ over $\Sigma$ is *inductive* for a transition relation $\delta$ over $\Sigma \uplus \Sigma'$ if

$$
I \wedge \delta \rightarrow I'
$$

is valid, where $I'$ is $I$ with every symbol replaced by its primed copy; validity is taken either over finite structures or over general (finite and infinite) structures.

**Theorem (Feldman, Padon, Immerman, Sagiv and Shoham).**

1. It is undecidable, given $I \in \forall^*\exists^*(\Sigma)$ and $\delta \in \mathrm{EPR}$, whether $I$ is inductive for $\delta$ over finite structures.
2. It is undecidable, given $I \in \forall^*\exists^*(\Sigma)$ and $\delta \in \mathrm{EPR}$, whether $I$ is inductive for $\delta$ over general structures.

For universal invariants the check reduces to unsatisfiability of an EPR sentence and is decidable.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Both proofs reduce from the halting problem through tiling problems, with the transition relation placing one tile per step on a board whose two dimensions are total orders axiomatized in EPR. Over finite structures the tiles encode the run of a Turing machine on a finite rectangle that must contain a halting tile at the end of a row, and the invariant is inductive exactly when no such halting tiling exists, that is, when the machine does not halt. Over general structures the reduction uses tilings of an infinite lower-triangular region, and the invariant is inductive exactly when no such infinite tiling exists, that is, when the machine halts. The two directions mirror Trakhtenbrot's theorem. A good expansion links pages for the undecidability of the halting-tiling problem on finite rectangles and of the lower-triangular infinite tiling problem.

## Sources

- Yotam M. Y. Feldman, Oded Padon, Neil Immerman, Mooly Sagiv and Sharon Shoham, *Bounded Quantifier Instantiation for Checking Inductive Invariants*, Logical Methods in Computer Science 15(3), 2019, https://doi.org/10.23638/LMCS-15(3:18)2019; the definitions of inductiveness and of the $\forall^*\exists^*$ and EPR classes, and the two undecidability theorems for inductiveness over finite structures and over general structures, read in arXiv:1710.08668v3. Locators in arXiv:1710.08668v3: Theorems A.1 and A.3.
