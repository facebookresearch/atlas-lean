# Topological temporal models and the spatio-temporal logic PTL × S4u

The spatio-temporal logic PTL × S4u combines propositional temporal logic with the topological logic S4u: regions evolve in time, and terms may apply Boolean, interior and temporal operators to regions; its fragments restrict which temporal operators may build terms.

**Topological temporal models.** A *flow of time* is a strict linear order $\mathfrak F = (W, <)$, such as $(\mathbb N, <)$, $(\mathbb Z, <)$ or a finite order. A *topological space* is a pair $\mathfrak T = (U, \mathbb I)$ of a nonempty set $U$ and an interior operator $\mathbb I$ on its subsets satisfying the Kuratowski axioms. A *topological temporal model* (tt-model) is a triple $\mathfrak M = (\mathfrak F, \mathfrak T, \mathfrak U)$ in which the valuation $\mathfrak U$ assigns to every spatial variable $p$ and time point $w \in W$ a set $\mathfrak U(p, w) \subseteq U$.

**Terms and formulas.** The spatio-temporal terms and the formulas of $\mathrm{PTL} \times \mathrm{S4}_u$ are

$$
\tau ::= p \mid \overline{\tau} \mid \tau_1 \sqcap \tau_2 \mid \mathbb I\tau \mid \tau_1\,\mathcal U\,\tau_2 \mid \tau_1\,\mathcal S\,\tau_2, \qquad \varphi ::= \boxdot\tau \mid \neg\varphi \mid \varphi_1 \wedge \varphi_2 \mid \varphi_1\,\mathcal U\,\varphi_2 \mid \varphi_1\,\mathcal S\,\varphi_2 .
$$

The valuation extends to terms by $\mathfrak U(\overline{\tau}, w) = U \setminus \mathfrak U(\tau, w)$, $\mathfrak U(\tau_1 \sqcap \tau_2, w) = \mathfrak U(\tau_1, w) \cap \mathfrak U(\tau_2, w)$, $\mathfrak U(\mathbb I\tau, w) = \mathbb I\,\mathfrak U(\tau, w)$, and

$$
\mathfrak U(\tau_1\,\mathcal U\,\tau_2, w) = \bigcup_{v > w}\Bigl(\mathfrak U(\tau_2, v) \cap \bigcap_{u \in (w, v)}\mathfrak U(\tau_1, u)\Bigr),
$$

with $\mathcal S$ the mirror image towards the past; on a discrete flow the next-time term $\bigcirc\tau$ has $\mathfrak U(\bigcirc\tau, w) = \mathfrak U(\tau, w + 1)$, and $\Diamond_F\tau$, $\Box_F\tau$ are the union and the intersection of the extensions of $\tau$ at all $v > w$. The formula $\boxdot\tau$ is true at $w$ iff $\mathfrak U(\tau, w) = U$; Booleans are as usual, and $\varphi_1\,\mathcal U\,\varphi_2$ is true at $w$ iff $\varphi_2$ is true at some $v > w$ and $\varphi_1$ at every $u \in (w, v)$ (dually for $\mathcal S$). A formula is *satisfiable* if it is true at some time point of some tt-model.

**Fragments and restrictions.** $\mathrm{PTL} \circ \mathrm{S4}_u$ allows only $\bigcirc$ among the temporal operators in terms, $\tau ::= p \mid \overline{\tau} \mid \tau_1 \sqcap \tau_2 \mid \mathbb I\tau \mid \bigcirc\tau$, with the full formula language; $\mathrm{PTL}_\Box \times \mathrm{S4}_u$ allows only $\Box_F$ and its past counterpart $\Box_P$, both in terms and in formulas. $\mathrm{LTL} \times \mathrm{S4}_u$ denotes the future fragment over the flow $(\mathbb N, <)$, and $\mathrm{LTL}_\Box \times \mathrm{S4}_u$ its restriction to $\Box_F$ and $\Diamond_F$. A tt-model satisfies the *finite state assumption* (FSA) if every spatio-temporal term takes only finitely many distinct sets as its extensions over time (the journal paper's formulation; the survey states the assumption for spatial variables, the form used for $\mathrm{LTL} \times \mathrm{S4}_u$).

## Depends on

- [Topological space](../../../../Topology/topological-spaces/topological-space.md)
- [Formulas of linear temporal logic](../../../temporal-logic/linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

$\mathrm{PTL} \times \mathrm{S4}_u$ contains propositional temporal logic and $\mathrm{S4}_u$, the logic of topological spaces with the universal modality, each of which is PSPACE-complete; its terms can describe how regions change over time, for example "the region where it will be raining ever and ever again", $\Box_F\Diamond_F\mathit{Rain}$. A $\mathrm{PTL} \times \mathrm{S4}_u$ formula is satisfiable in a tt-model with FSA iff it is satisfiable in one based on a finite (Aleksandrov) topological space.

## Sources

- D. Gabelaia, R. Kontchakov, A. Kurucz, F. Wolter and M. Zakharyaschev, "Combining spatial and temporal logics: expressiveness vs. complexity", *Journal of Artificial Intelligence Research* 23:167–243, 2005, <https://doi.org/10.1613/jair.1537>; read in the open-access author copy at <https://kuag19.github.io/homepage/gkkwz.pdf>: Section 3.1 (tt-models), Section 3.2 (the language $\mathrm{PTL} \times \mathrm{S4}_u$, its semantics, the FSA, Proposition 3.4, and the fragments $\mathrm{PTL} \circ \mathrm{S4}_u$ and $\mathrm{PTL}_\Box \times \mathrm{S4}_u$).
- R. Kontchakov, A. Kurucz, F. Wolter and M. Zakharyaschev, "Spatial logic + temporal logic = ?", in *Handbook of Spatial Logics*, Springer, 2007, pp. 497–564, <https://doi.org/10.1007/978-1-4020-5587-4_9>; read in the open-access author copy at <https://kuag19.github.io/homepage/st.pdf>: Section 4 (the languages $\mathrm{LTL} \times \mathrm{S4}_u$ and $\mathrm{LTL}_\Box \times \mathrm{S4}_u$ over $(\mathbb N, <)$, finite tt-models and the FSA).
