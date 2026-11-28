# Double-redundancy lattice and the fifteen-for-free property

**Redundancy lattice.** For two variables let $\mathcal A = \{\{1\}, \{2\}, \{1,2\}, \{\{1\},\{2\}\}\}$ be the antichains of nonempty subsets of $\{1,2\}$, ordered by $\alpha \preceq \beta$ iff for every $b \in \beta$ there is $a \in \alpha$ with $a \subseteq b$ (the Williams–Beer lattice of partial information decomposition, PID).

**Product lattice.** For a two-component process with past $X = (X_t^1, X_t^2)$ and future $Y = (X_{t+1}^1, X_{t+1}^2)$, the nodes are $\alpha \to \beta$ with $\alpha, \beta \in \mathcal A$, ordered by $\alpha\to\beta \preceq \alpha'\to\beta'$ iff $\alpha \preceq \alpha'$ and $\beta \preceq \beta'$; this is a lattice with $16$ nodes.

**Double redundancy.** A double-redundancy function assigns $I_\cap^{\alpha\to\beta}$, the information common to the sources in $\alpha$ that is seen in the targets in $\beta$, subject to:

- **Axiom 1 (compatibility).** For $\alpha = \{\alpha_1, \dots, \alpha_J\}$, $\beta = \{\beta_1, \dots, \beta_K\}$: if $K = 1$, $I_\cap^{\alpha\to\beta} = \mathrm{Red}(X^{\alpha_1}, \dots, X^{\alpha_J}; Y^{\beta_1})$; if $J = 1$, $I_\cap^{\alpha\to\beta} = \mathrm{Red}(Y^{\beta_1}, \dots, Y^{\beta_K}; X^{\alpha_1})$; if $J = K = 1$, $I_\cap^{\alpha\to\beta} = I(X^{\alpha_1}; Y^{\beta_1})$, where $\mathrm{Red}$ is a single-target PID redundancy function.
- **Axiom 2 (subset equality).** Adding to $\alpha$ (or $\beta$) a superset of one of its elements does not change $I_\cap^{\alpha\to\beta}$.

**Atoms.** The atoms $I_\partial^{\alpha\to\beta}$ are defined by Möbius inversion on the product lattice:

$$I_\cap^{\alpha\to\beta} = \sum_{\alpha'\to\beta' \preceq \alpha\to\beta} I_\partial^{\alpha'\to\beta'}, \qquad I_\partial^{\alpha\to\beta} = I_\cap^{\alpha\to\beta} - \sum_{\alpha'\to\beta' \prec \alpha\to\beta} I_\partial^{\alpha'\to\beta'} .$$

**Definition 1 (ΦID).** For Markovian dynamics, the integrated information decomposition is the collection of the $16$ atoms, which sum to the time-delayed mutual information: $I(X; Y) = \sum_{\alpha,\beta\in\mathcal A} I_\partial^{\alpha\to\beta}$.

**Proposition 1 (fifteen for free).** Axioms 1 and 2 determine all $16$ atoms uniquely once one specifies (i) a single-target redundancy function $\mathrm{Red}$ and (ii) the double-redundancy atom $I_\partial^{\{1\}\{2\}\to\{1\}\{2\}}$.

## Expansion

The top node $\{12\}\to\{12\}$ carries the full $I(X;Y)$, so the atoms below it partition it. Axioms 1 and 2 express every $I_\cap^{\alpha\to\beta}$ except $I_\cap^{\{1\}\{2\}\to\{1\}\{2\}}$ through PID redundancies or mutual informations; the linear system relating the $16$ redundancies to the $16$ atoms is triangular in the lattice order, so fixing the one missing quantity fixes all atoms. This mirrors PID, where choosing $\mathrm{Red}$ yields the unique and synergistic terms. Atoms are indexed by whether information is carried redundantly, uniquely or synergistically in the past and in the future, which separates storage, transfer (e.g. $\mathrm{Un}^1 \to \mathrm{Un}^2$), downward causation ($\mathrm{Syn} \to \mathrm{Un}$, $\mathrm{Syn} \to \mathrm{Red}$), upward causation ($\mathrm{Un} \to \mathrm{Syn}$, $\mathrm{Red} \to \mathrm{Syn}$) and synergistic storage ($\mathrm{Syn} \to \mathrm{Syn}$). Active information storage, transfer entropy, causal density and whole-minus-sum integrated information are then sums of atoms; the last counts some atoms twice and some with a negative sign, so systems with equal integrated information can integrate it in qualitatively different ways. Concrete double-redundancy measures extend Ince's common-change-in-surprisal and Barrett's minimum-mutual-information redundancy.

## Sources

- P. A. M. Mediano, F. E. Rosas, A. I. Luppi, R. L. Carhart-Harris, D. Bor, A. K. Seth and A. B. Barrett, "Toward a unified taxonomy of information dynamics via Integrated Information Decomposition", Proceedings of the National Academy of Sciences of the USA 122(39) (2025) e2423297122, Eqs. (5)–(11), Axioms 1–2, Definition 1 and Proposition 1, <https://doi.org/10.1073/pnas.2423297122>, PMCID PMC12501198.
