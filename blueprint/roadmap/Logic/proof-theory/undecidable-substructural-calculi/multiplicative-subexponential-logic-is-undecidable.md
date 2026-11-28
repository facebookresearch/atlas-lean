# Multiplicative subexponential logic with two linear subexponentials is undecidable

Classical propositional multiplicative linear logic extended with one unrestricted subexponential and two incomparable linear subexponentials below it can encode two-register Minsky machines, so its derivability problem is undecidable.

**Subexponential logic.** A *subexponential signature* $\Sigma=\langle I,U,\le\rangle$ consists of a countable set $I$ of labels, a set $U\subseteq I$ of *unbounded* labels, and a preorder $\le$ on $I$ that is upward closed with respect to $U$ (if $u\in U$ and $u\le v$ then $v\in U$). *Multiplicative subexponential logic* $\mathrm{MSEL}_\Sigma$ is classical propositional multiplicative linear logic, with the connectives $\otimes$, $\mathbf 1$, par (⅋), $\bot$ and linear negation, extended by subexponential modalities $!^u$ and $?^u$ for each label $u\in I$, in a one-sided sequent calculus: the promotion rule for $!^u$ requires every other formula of the sequent to be of the form $?^v A$ with $u\le v$, dereliction is available for every label, and weakening and contraction are allowed exactly for $?^u$ with $u\in U$. With $I=U=\{\infty\}$ this is multiplicative exponential linear logic (MELL), whose decidability is a long-standing open problem.

Let $\Xi$ be the signature with labels $\{\infty,a,b\}$, unbounded labels $\{\infty\}$, and $\le$ the reflexive-transitive closure of $a\le\infty$ and $b\le\infty$; so $a$ and $b$ are incomparable linear labels below one unrestricted label.

**Theorem (Chaudhuri).** Derivability of $\mathrm{MSEL}_\Xi$ sequents is recursively unsolvable (Corollary 12 of the source).

Additives are not needed: the undecidability of multiplicative-additive exponential linear logic uses the additives, while here the two linear subexponentials take their place. Multiplicative linear logic without exponentials is decidable.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

A configuration of a two-register Minsky machine with state $q$ and register values $v_a,v_b$ is encoded as a context with one atom for $q$ and $v_a$ copies of $?^a\bar a$ and $v_b$ copies of $?^b\bar b$, the registers being kept as linear resources under the incomparable labels $a$ and $b$, while the machine's instructions are stored as formulas under the unbounded label $\infty$ and can be used any number of times. Increment and decrement instructions add or consume one copy, and a zero test is implemented with a promotion of $!^a$ or $!^b$: promotion is possible only when the rest of the context consists of $?$-formulas with labels above the promoted one, so it succeeds exactly when the other register's resources are absent. Using a focused proof system for $\mathrm{MSEL}$, a sequent built from the encoding is derivable exactly when the machine halts from the encoded configuration. A good expansion links a page for the completeness of the focused calculus for subexponential logic.

## Sources

- K. Chaudhuri, "Undecidability of multiplicative subexponential logic", in *Proceedings of the Third International Workshop on Linearity (LINEARITY 2014)*, Electronic Proceedings in Theoretical Computer Science 176, pp. 1–8, 2015, doi:[10.4204/EPTCS.176.1](https://doi.org/10.4204/EPTCS.176.1); read in arXiv:1502.04769v1 ([arXiv](https://arxiv.org/abs/1502.04769v1)): Definition 1 (subexponential signatures) and the definition of $\mathrm{MSEL}$, Definition 3 (two-register machines), Definition 5 (the signature $\Xi$), Definitions 6 to 8 (the encoding), and Corollary 12.
