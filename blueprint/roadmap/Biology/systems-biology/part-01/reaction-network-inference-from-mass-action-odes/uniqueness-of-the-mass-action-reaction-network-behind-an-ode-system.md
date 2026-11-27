# Uniqueness of the mass-action reaction network behind an ODE system

**Networks and their ODEs.** A reaction network on species $x_1, \dots, x_n$ is a finite set of reactions $r$, each with reactant stoichiometry $a_r \in \mathbb{Z}_{\ge 0}^n$, product stoichiometry $b_r \in \mathbb{Z}_{\ge 0}^n$ and a rate law $f_r(x)$. It generates the ODE system

$$\frac{dx_s}{dt} = \sum_r (b_{r,s} - a_{r,s})\, f_r(x), \qquad s = 1, \dots, n .$$

**Conditions.**

1. (Mass action with symbolic parameters.) $f_r(x) = k_r \prod_s x_s^{a_{r,s}}$, where each $k_r$ is a symbol from a finite alphabet of parameters (not a numerical value).
2. (No void reactions.) $a_r \ne b_r$ for every $r$.
3. (Distinct parameters for equal reactants.) If $r \ne r'$ and $a_r = a_{r'}$, then $k_r \ne k_{r'}$.

Under Condition 1 the generated right-hand sides are polynomials in $x$ whose coefficients are integer linear combinations of the symbols $k_r$:

$$\frac{dx_s}{dt} = \sum_{j} c_{j,s}\, k_j \prod_{t} x_t^{a_{j,t}}, \qquad c_{j,s} \in \mathbb{Z} .$$

**Theorem.** For any ODE system of this form there is at most one reaction network satisfying Conditions 1–3 that generates it, up to elementary algebraic rewriting. When it exists it is obtained constructively: each distinct pair (parameter $k_j$, monomial $x^{a_j}$) is one reaction $j$ with reactants $a_j$, and its products are

$$b_{j,s} = a_{j,s} + c_{j,s}, \qquad s = 1, \dots, n .$$

If some $b_{j,s} < 0$, no network satisfying the conditions generates the system; for example, $\dot x = -2kx$ would need a reaction with one copy of $x$ as reactant and $-1$ copies as product.

## Depends on

- [Chemical reaction network](../../../../Dynamics/smooth-dynamics/reaction-network.md)
- [Mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md)

## Expansion

Two lemmas carry the proof. First, every reaction's term appears in some equation: since $a_r \ne b_r$ there is a species with non-zero net change, and because parameters are symbolic, a term $k_r x^{a_r}$ could only be cancelled by another term with the same parameter and the same monomial, which Condition 3 forbids. Second, every term $k_j x^{a_j}$ of the ODEs comes from a reaction with parameter $k_j$ and reactant vector $a_j$, and by Condition 3 from exactly one such reaction, so terms sharing parameter and monomial are merged. Hence the reactions and their reactants are determined by the ODEs, and the net stoichiometry $b_j - a_j = c_j$ then fixes the products. The conditions are necessary for uniqueness: with general kinetics, or with numeric instead of symbolic rate constants, or with one parameter shared by two reactions with the same reactants, different networks give the same ODEs. The result extends to Michaelis–Menten terms $V x/(K + x)$ via the uniqueness of partial-fraction decomposition of rational right-hand sides. Once the network is recovered, structural analyses that need it (invariants, elementary modes, deficiency-based tests) become applicable to models given only as ODEs.

## Sources

- S. Soliman, M. Heiner, "A unique transformation from ordinary differential equations to reaction networks", PLoS ONE 5 (2010) e14284, Methods (Conditions 1–3, Lemmas 1–2, Theorem 1, Example 4, section "Beyond Mass Action Law"), <https://doi.org/10.1371/journal.pone.0014284> (PMC3008708).
