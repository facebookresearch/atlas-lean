# Model checking parametric timed CTL over one-clock parametric timed automata is undecidable

When parameters may occur both in a discrete-time timed automaton with one parametric clock and in the timed CTL formula, and the formula may use equality constraints, no algorithm decides the model checking problem.

**Parametric timed automata.** Fix a finite set $\Theta$ of parameters ranging over $\mathbb N$ and a single clock $x$. A *parametric timed automaton* $\mathsf A=(Q,E,\mathsf L,\mathsf I)$ has a finite set $Q$ of states, edges $E\subseteq Q\times\{0,1\}\times\mathsf G\times2^{\{x\}}\times Q$ carrying a time increment $\tau\in\{0,1\}$, a guard from the set $\mathsf G$ of conjunctions of comparisons of $x$ with linear terms over $\Theta$, and an optional reset of $x$, a labeling $\mathsf L$ of states by atomic propositions and an invariant $\mathsf I(q)\in\mathsf G$ for each state. Time is discrete: under a parameter valuation $v$, a transition $(q,x)\xrightarrow{\tau}(q',x')$ adds $\tau$ to the clock, tests the guard and invariants under $v$, and then resets $x$ if required; runs are infinite and non-Zeno.

**Parametric timed CTL.** A PTCTL formula is a block of quantifiers over parameters followed by a quantifier-free temporal formula built from atomic propositions, comparisons of linear terms over the parameters, Boolean connectives, $\mathsf{EX}$, and the timed until operators $\varphi\,\mathsf{EU}_{\sim\alpha}\,\varphi$ and $\varphi\,\mathsf{AU}_{\sim\alpha}\,\varphi$, where $\sim\in\{<,\le,=,\ge,>\}$ and $\alpha$ is a linear term over the parameters; $\varphi\,\mathsf{EU}_{\sim\alpha}\,\psi$ holds at a configuration if some run reaches, after a duration $t$ with $t\sim\alpha$, a configuration satisfying $\psi$, with $\varphi$ holding before. The *model checking problem* asks, given $\mathsf A$, a configuration $(q,x_0)$ and a PTCTL sentence $f$, whether $(q,x_0)\models f$.

**Theorem (Bruyère and Raskin).** For every sentence $\Phi$ of Presburger arithmetic with divisibility one can construct a parametric timed automaton $\mathsf A$ with one parametric clock, a configuration $(q,x_0)$ and a PTCTL formula $f$ such that $\Phi$ is true if and only if $(q,x_0)\models f$. Consequently, the model checking problem for PTCTL over discrete-time parametric timed automata with one parametric clock is undecidable.

The formulas produced use only the subscript $=$ in the timed until operators, and equality is what causes undecidability: for the fragment of PTCTL without equality in these subscripts, the source shows that model checking and parameter synthesis are decidable.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Presburger arithmetic with divisibility, the first-order theory of $(\mathbb N;+,<,\mid)$, is undecidable (Bès). Put $\Phi$ in prenex normal form with atoms $z=\alpha$, $z>\alpha$ and $z\mid z'$, and let the quantified variables be the parameters. Atoms $z=\alpha$ and $z>\alpha$ are already PTCTL formulas. For a divisibility atom $z\mid z'$ one uses a small automaton with an initial state $i$ and a final state $f$ in which a run from $(i,0)$ to $(f,z)$ of duration $D$ exists exactly when $z$ divides $D$, so the atom becomes $\sigma_1\wedge\mathsf{EF}_{=z'}\,\sigma_2$ with $\sigma_1,\sigma_2$ labeling $i$ and $f$. The automata for the divisibility atoms are merged at their initial states, final states lead to a sink with a time-progress loop, and the quantifier prefix of $\Phi$ is copied onto the parameters. A good expansion links a page for the undecidability of Presburger arithmetic with divisibility.

## Sources

- V. Bruyère and J.-F. Raskin, "Real-time model-checking: parameters everywhere", *Logical Methods in Computer Science* 3(1), paper 7, 2007, doi:[10.2168/LMCS-3(1:7)2007](https://doi.org/10.2168/LMCS-3(1:7)2007); read in arXiv:cs/0701138v2 ([arXiv](https://arxiv.org/abs/cs/0701138v2)): Definitions 2.2 to 2.5 (parametric timed automata and PTCTL) in Section 2, and Theorem 3.2 with its proof, Corollary 3.3, Remark 3.4 (equality) and Corollary 3.11 (the fragment F-PTCTL) in Section 3.
