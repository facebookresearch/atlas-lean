# Action logic and infinitary action logic

Action logic $\mathbf{ACT}$ is the inequational theory of residuated Kleene lattices, presented as the multiplicative-additive Lambek calculus with cut plus fixed-point rules for the Kleene star; infinitary action logic $\mathbf{ACT}_\omega$ replaces the star rules by an $\omega$-rule and is the logic of $*$-continuous action lattices.

**Formulas and sequents.** Formulas are built from variables and the constants $\mathbf{0}$, $\mathbf{1}$ with product $\cdot$, the residuals $\backslash$ and $/$, the lattice operations $\wedge$, $\vee$ and the Kleene star ${}^*$. A sequent $\alpha_1, \dots, \alpha_n \to \beta$ (with $n \geq 0$; the empty antecedent is written $\Lambda$) is read as $\alpha_1 \cdots \alpha_n \preceq \beta$, and $\Lambda \to \beta$ as $\mathbf{1} \preceq \beta$.

**$\mathbf{MALC}$.** The multiplicative-additive Lambek calculus has the axiom $\alpha \to \alpha$, the axioms $\Gamma, \mathbf{0}, \Delta \to \gamma$ and $\Lambda \to \mathbf{1}$, and the usual left and right introduction rules for $\mathbf{1}$, $\cdot$, $\backslash$, $/$, $\wedge$ and $\vee$ (with empty antecedents allowed).

**$\mathbf{ACT}$** is $\mathbf{MALC}$ plus cut and the star rules

$$
\frac{\Lambda \to \beta \qquad \alpha, \beta \to \beta}{\alpha^* \to \beta}, \qquad \frac{}{\Lambda \to \alpha^*}, \qquad \frac{\Pi \to \alpha \qquad \Delta \to \alpha^*}{\Pi, \Delta \to \alpha^*}.
$$

**$\mathbf{ACT}_\omega$** is $\mathbf{MALC}$ plus the $\omega$-rule and the right star rules

$$
\frac{\big(\Gamma, \alpha^n, \Delta \to \gamma\big)_{n \in \omega}}{\Gamma, \alpha^*, \Delta \to \gamma}, \qquad \frac{\Pi_1 \to \alpha \quad \cdots \quad \Pi_n \to \alpha}{\Pi_1, \dots, \Pi_n \to \alpha^*} \ (n \in \omega),
$$

where $\alpha^n$ is $n$ copies of $\alpha$; its derivations are well-founded but possibly infinite trees, and cut is admissible in it (Palka). Each calculus is sound and complete for its class of algebras: action lattices (residuated Kleene lattices) for $\mathbf{ACT}$ and $*$-continuous ones, where $a \cdot b^* \cdot c = \sup_n a \cdot b^n \cdot c$, for $\mathbf{ACT}_\omega$. Every sequent derivable in $\mathbf{ACT}$ is derivable in $\mathbf{ACT}_\omega$.

A *logic between* $\mathbf{ACT}$ and $\mathbf{ACT}_\omega$ is any set $\mathcal{L}$ of sequents with $\mathbf{ACT} \subseteq \mathcal{L} \subseteq \mathbf{ACT}_\omega$; no closure conditions are required.

## Depends on

- [Derivability in the Lambek calculus](../../../TheoryOfComputation/np-completeness/strings-and-puzzles/lambek-calculus-derivability/derivable.md)

## Proof depends on

None.

## Expansion

$\mathbf{ACT}$ is recursively enumerable, being given by finitary rules. Buszkowski and Palka (2007) proved that $\mathbf{ACT}_\omega$ is $\Pi^0_1$-complete. No cut-free calculus for $\mathbf{ACT}$ is known.

## Sources

- S. Kuznetsov, "Action logic is undecidable", *ACM Transactions on Computational Logic* 22(2):1–26, 2021, doi:10.1145/3445810; read as arXiv:1912.11273v1, <https://arxiv.org/abs/1912.11273v1>: Section 1.2 (the calculi $\mathbf{MALC}$, $\mathbf{ACT}$ and $\mathbf{ACT}_\omega$) and Section 1.1 (the algebraic semantics).
