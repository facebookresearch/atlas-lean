# Operator product reduction for graph grammar rules

In a stochastic parameterized graph grammar, each rewrite rule $r: G^{\mathrm{in}}_r \to G^{\mathrm{out}}_r$ between labelled graphs acts on probability distributions over labelled graphs through a state-change operator $\hat W_r$, built from creation and annihilation operators for nodes, node labels and links, with a rate factor $\rho_r$ and a multiplicative normalization $C_r$; the full probability-conserving operator is $W_r = \hat W_r - D_r$ with a diagonal loss term $D_r$.

**Theorem (product of two rule operators).** Under either the hanging-edge-permissive semantics or the hanging-edge-removal semantics (assuming finitely many rules, index allocation blocks and firings),

$$\hat W_{G^{\mathrm{in}}_{r_2} \to G^{\mathrm{out}}_{r_2}}\, \hat W_{G^{\mathrm{in}}_{r_1} \to G^{\mathrm{out}}_{r_1}} \simeq \sum_{\substack{H \subseteq G^{\mathrm{out}}_{r_1},\ \tilde H \subseteq G^{\mathrm{in}}_{r_2} \\ H \cong \tilde H \text{ edge-maximal}}} \;\sum_{h: H \to \tilde H} \hat W_{G^{\mathrm{in}}_{1;2}(\tilde H) \to_h G^{\mathrm{out}}_{1;2}(H)},$$

where $h$ ranges over label-preserving isomorphisms, and the compound rule has input $G^{\mathrm{in}}_{r_1} \sqcup (G^{\mathrm{in}}_{r_2} \setminus \tilde H)$ and output $G^{\mathrm{out}}_{r_2} \sqcup (G^{\mathrm{out}}_{r_1} \setminus H)$, with links glued along $h$ (Mjolsness 2022, Theorems 1 and 2, Eqs. 33–35 and 48). All coefficients are nonnegative integers.

**Corollaries.** The same reduction holds for the probability-conserving operators $W_r$ with integer coefficients, and the commutator $[\hat W_{r_2}, \hat W_{r_1}]$ reduces to an integer combination of single-rule operators in which the $H = \emptyset$ summand (independent, non-overlapping firings) cancels (Corollaries 1, 2, 4, 5, 6, 8). Thus rule operators generate an algebra closed under products and commutators, analogous to the structure constants of a Lie algebra.

## Expansion

Writing each rule operator as a product of link annihilators for $G^{\mathrm{in}}$ and link creators for $G^{\mathrm{out}}$, the product $\hat W_{r_2}\hat W_{r_1}$ requires commuting the annihilators of $r_2$ past the creators of $r_1$. The link commutation relations split this into a sum over the subgraph $H$ of $r_1$'s output that $r_2$'s input consumes, with a link-checking factor implementing graph matching on $H$ (Lemma 1). Each summand is itself a single rewrite rule whose input and output are the glued compound graphs. Under hanging-edge removal the extra edge-deletion factors commute through and do not change the formula.

## Sources

- E. Mjolsness, *Explicit calculation of structural commutation relations for stochastic and dynamical graph grammar rule operators in biological morphodynamics*, Frontiers in Systems Biology 2 (2022), 898858, Sections 3.4–3.5, Lemma 1, Theorems 1–2 and Corollaries 1–8. <https://doi.org/10.3389/fsysb.2022.898858> (PMCID: PMC9879069)
