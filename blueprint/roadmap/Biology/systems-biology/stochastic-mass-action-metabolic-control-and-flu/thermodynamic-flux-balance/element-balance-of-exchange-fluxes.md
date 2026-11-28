# Element-balance obstruction to flux-balance feasibility

Exchange bounds can make a flux balance problem infeasible before any objective is optimized: the allowed exchanges must carry the conserved quantities required by the right-hand side. A zero value assigned to an empty problem is not an attained optimum.

Let $M$ (modelled species or reactants) and $R$ (reactions) be finite, $S\in\mathbb{R}^{M\times R}$,
$R=I\sqcup E$ an internal/exchange split, and $A\in\mathbb{R}^{K\times M}$ a composition matrix for
quantities conserved by the chosen representation. Suppose every internal reaction is
[balanced](../../../../Chemistry/amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md)
for $A$: $AS_{\cdot r}=0$ for $r\in I$.

Choose the rows of $A$ consistently. For chemical equations on species, they may include all elements
and electric charge. For biochemical equations at specified pH, use the transformed conservation
matrix, omitting hydrogen and charge rows; at specified pMg omit magnesium as well. A pseudoisomer
group need not have a fixed charge or hydrogen count. Do not combine chemical-species columns and
transformed-reactant columns under one unadjusted conservation matrix.

For every $v\in\mathbb{R}^R$ and $b\in\mathbb{R}^M$ with $Sv=b$,

$$
\sum_{x\in E}v_x\,AS_{\cdot x}=Ab.
$$

Consequently, if no exchange vector $(v_x)_{x\in E}$ within the specified flux bounds satisfies this
identity, the set of [feasible fluxes](../fba-feasible.md) is empty. The
[optimal value](../fba-value.md) $V(b)=0$ is then the empty-set convention, not an optimum. At steady
state ($b=0$), the same identity requires element-balanced exchanges.

**Witness.** Let species $G$ have one carbon and $P$ two, with internal reaction $2G\to P$, balanced
for $A=(1\ \ 2)$. Bound uptake of $G$ by $u\in[0,1]$ and secretion of $P$ by $p\in[1,2]$. A steady
flux requires $u=2p$, impossible under these bounds. The problem is infeasible regardless of the objective.

## Depends on

- [Balanced reaction for a composition matrix](../../../../Chemistry/amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md)
- [Feasible fluxes of flux balance analysis](../fba-feasible.md)
- [Optimal value of flux balance analysis](../fba-value.md)

## Proof depends on

- [Balanced reaction for a composition matrix](../../../../Chemistry/amounts-and-stoichiometry/balanced-reactions-and-stoichiometric-conservati/is-balanced.md)
- [Open elemental balance](../../../../Chemistry/amounts-and-stoichiometry/process-material-balances/open-elemental-balance.md)
- [Feasible fluxes of flux balance analysis](../fba-feasible.md)
- [Optimal value of flux balance analysis](../fba-value.md)

## Expansion

This is the exchange-flux specialization of the open elemental balance. Algebraically, multiply
$Sv=b$ by $A$: $Ab=\sum_{r\in I}v_rAS_{\cdot r}+\sum_{x\in E}v_xAS_{\cdot x}$, and the internal
terms vanish. If the identity has no solution within the exchange bounds, no flux satisfies the full
balance and bounds. In the witness, the species balances are $u-2w=0$ and $w-p=0$, where $w$ is the
internal flux; they imply $u=2p$. The empty-value convention supplies no feasible witness.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff,
  *Recommendations for terminology and databases for biochemical thermodynamics*, Biophysical Chemistry
  155 (2011), 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Section and equation numbers are from
  the IUBMB-hosted author manuscript (August 2010, 53 pages),
  <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 2 after Equation (2-3)
  (specified pH and charge balance), Section 8, Equations (8-4) and (8-7)–(8-10)
  (chemical and transformed conservation matrices), and Section 13 (do not intermingle chemical and
  biochemical reaction conventions).
