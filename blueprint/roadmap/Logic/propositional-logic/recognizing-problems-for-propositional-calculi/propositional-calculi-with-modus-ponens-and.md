# Propositional calculi with modus ponens and substitution

A propositional calculus in the sense of Tarski's decision problems is a finite set of axioms over a finite signature containing implication; its theorems are the formulas derivable from the axioms by modus ponens and substitution. Comparing such calculi by their sets of theorems gives the recognizing problems for extensions, completeness and axiomatizations.

**Calculi.** Fix an infinite set of propositional variables and a finite signature $\Sigma$ of connectives containing the binary connective $\to$. A *$\Sigma$-calculus* $P$ is a finite set of $\Sigma$-formulas (its axioms) together with two rules of inference:

$$
A,\ A \to B \ \vdash\ B \quad (\text{modus ponens}), \qquad A \ \vdash\ \sigma A \quad (\text{substitution}),
$$

where $\sigma A$ is any substitution instance of $A$. $[P]$ is the set of formulas derivable in $P$, and $P \vdash A$ means $A \in [P]$.

**Order.** $P_1 \leq P_2$ (equivalently $P_2 \geq P_1$) means $[P_1] \subseteq [P_2]$, and $P_1 \sim P_2$ means $[P_1] = [P_2]$. $\mathbf{Int}_{\{\to\}}$ is the intuitionistic implicational calculus with axioms $x \to (y \to x)$ and $(x \to (y \to z)) \to ((x \to y) \to (x \to z))$; $\mathbf{Cl}_{\{\to\}}$ adds Peirce's law $((x \to y) \to x) \to x$.

**Recognizing problems.** For a fixed $\Sigma$-calculus $P_0$, the input is a $\Sigma$-calculus $P$, and the question is:

- **Drv** (recognizing derivations): is $P \leq P_0$?
- **Ext** (recognizing extensions): is $P_0 \leq P$?
- **Axm** (recognizing axiomatizations): is $P \sim P_0$?
- **Cmpl** (recognizing completeness): given $P$ with $P \leq P_0$, is $P_0 \leq P$?

## Depends on

None.

## Proof depends on

None.

## Expansion

Since $P \leq P_0$ holds iff $P_0$ derives each axiom of $P$, these problems compare finitely axiomatized theories. Linial and Post (1949) proved Axm, Ext and Cmpl undecidable for classical logic over $\{\neg, \vee\}$, Kuznetsov (1963) for every calculus containing intuitionistic logic over $\{\neg, \vee, \wedge, \to\}$, and Marcinkowski (1994) proved Ext undecidable for the one-axiom calculus $\{A\}$ for every implicational tautology $A$ not of the form $B \to B$.

## Sources

- Grigoriy V. Bokov, "Undecidable problems for propositional calculi with implication", *Logic Journal of the IGPL* 24(5):792–806, 2016, doi:10.1093/jigpal/jzw013; read as arXiv:1502.00978v1, <https://arxiv.org/abs/1502.00978v1>: Section 2 (calculi, the order $\leq$, the problems Drv, Ext, Axm and Cmpl, and Theorems 2.1–2.4) of arXiv:1502.00978v1.
- Grigoriy V. Bokov, "Undecidability of the problem of recognizing axiomatizations for propositional calculi with implication", *Logic Journal of the IGPL* 23(2):341–353, 2015, doi:10.1093/jigpal/jzu047; read as arXiv:1407.7010v1, <https://arxiv.org/abs/1407.7010v1>: Section 2 (the axioms of $\mathbf{Int}_{\{\to\}}$ and $\mathbf{Cl}_{\{\to\}}$) of arXiv:1407.7010v1.
