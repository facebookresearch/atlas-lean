# Monodic standpoint ALCOIF with one rigid role is undecidable

Monodic standpoint extensions of expressive description logics keep the complexity of the underlying logic, but forcing a single role to be interpreted identically in all precisifications already makes TBox satisfiability undecidable in the presence of inverses, functionality and nominals.

**Theorem (Gómez Álvarez and Rudolph).** A *standpoint structure* $\mathfrak M = \langle\Delta, \Pi, \sigma, \gamma\rangle$ has a nonempty domain $\Delta$, a nonempty set $\Pi$ of precisifications, a map $\sigma$ from standpoint symbols to subsets of $\Pi$ with $\sigma(*) = \Pi$ for the universal standpoint $*$, and a map $\gamma$ assigning to each $\pi \in \Pi$ a first-order interpretation over $\Delta$ of concept names, role names and constants, constants being interpreted identically in all precisifications. A role name $E$ is *rigid* in $\mathfrak M$ if $E^{\gamma(\pi)}$ is the same for all $\pi \in \Pi$. In *monodic standpoint ALCOIF*, $\mathbb S^{\mathrm{mon}}_{\mathcal{ALCOIF}}$, concepts are

$$
C, D ::= A \mid \neg C \mid \{o\} \mid C \sqcap D \mid \exists R.C \mid \lozenge_e C, \qquad R ::= P \mid P^-,
$$

with concept names $A$, constants $o$, role names $P$ and standpoint expressions $e$ (Boolean combinations of standpoint symbols), where $(\lozenge_e C)$ at $\pi$ is the set of elements in $C$ at some $\pi' \in \sigma(e)$, and $\square_e C = \neg\lozenge_e\neg C$; a *TBox* is a finite set of general concept inclusions $C \sqsubseteq D$ together with functionality statements $\mathit{func}(P)$, that is $\top \sqsubseteq \neg{\geqslant}2\,P.\top$. A TBox is satisfiable if some standpoint structure satisfies all its axioms in every precisification. Satisfiability of $\mathbb S^{\mathrm{mon}}_{\mathcal{ALCOIF}}$ TBoxes in which one distinguished role name is required to be rigid is undecidable, even for TBoxes with just one nominal and one functionality statement (Theorem 29 of the source). The proof reduces the problem whether, for a fixed tiling system $T_{\mathrm{und}}$, a given initial condition extends to a tiling of $\mathbb N \times \mathbb N$.

Without the rigid role, satisfiability of monodic standpoint $\mathcal{ALCOIQB}^{\mathsf{Self}}$, $\mathcal{SHOIQB}_s$ and $\mathcal{SROIQB}_s$ has the same complexity as for the underlying description logics, so the standpoint extension of OWL is complexity-neutral; rigidity of a role $E$ is expressed by the first-order standpoint formula $\forall x, y.\,(E(x, y) \to \square_* E(x, y))$, which is not monodic. By contrast, as the source recalls after its proof, satisfiability of ALCIQ TBoxes with arbitrarily many rigid roles and one S5 modality allowed in front of concept and role expressions is decidable in 2EXPTIME (Artale, Lutz and Toman).

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the tiling of $\mathbb N \times \mathbb N$ with a given initial condition for a fixed tiling system. The rigid role $E$ represents both horizontal and vertical grid edges, distinguished by rigid markers for even and odd rows, and the functional role $\mathit{Point}$ points into the domain from the nominal $o$. The inclusions

$$
\top \sqsubseteq \exists E.\square_*\mathit{Even} \sqcap \exists E.\square_*\mathit{Odd} \sqcap \lozenge_*\mathit{Pick},
$$

$$
\mathit{Pick} \sqsubseteq \forall E.\bigl(\neg\mathit{Even} \sqcup \forall E.(\neg\mathit{Odd} \sqcup \exists\mathit{Point}^-.\{o\})\bigr), \qquad \mathit{Pick} \sqsubseteq \forall E.\bigl(\neg\mathit{Odd} \sqcup \forall E.(\neg\mathit{Even} \sqcup \exists\mathit{Point}^-.\{o\})\bigr)
$$

ensure that each grid element is picked in some precisification, and there the upper neighbor of its right neighbor and the right neighbor of its upper neighbor are both pointed to by $o$ through the functional role, so they coincide. Since $E$ is rigid, these coincidences hold in all precisifications and the grid closes; a tiling on top of the grid is enforced very similarly to the source's earlier lower-bound construction. The problem reduced is the one Section 5 of the source states: "There is a tiling system $T_{\mathrm{und}}$ such that the following problem is undecidable: Given an initial condition of size $n$, is there a corresponding $T_{\mathrm{und}}$-tiling of $\mathbb N\times\mathbb N$?" The linked tiling page, with the tile set as input and no initial condition, does not give this; a good expansion links a page for undecidability of tiling with initial conditions for one fixed tiling system, which follows by simulating a universal Turing machine in a fixed tile set and using the undecidability of halting.

## Sources

- L. Gómez Álvarez and S. Rudolph, "Putting Perspective into OWL [sic]: Complexity-Neutral Standpoint Reasoning for Ontology Languages via Monodic S5 over Counting Two-Variable First-Order Logic", in *Proceedings of the 22nd International Conference on Principles of Knowledge Representation and Reasoning (KR 2025)*, 2025, pp. 366–375, <https://doi.org/10.24963/kr.2025/36>; read as arXiv:2508.00653v1, <https://arxiv.org/abs/2508.00653v1>, whose numbering is used here: Section 2 ("Preliminaries": first-order standpoint logic, standpoint structures, rigid predicates) and Section 5 ("Nominals Cause Trouble": the fragment $\mathbb S^{\mathrm{mon}}_{\mathcal{ALCOIF}}$ and the tiling problems), with Theorem 29 in Section 5.2 ("Lifting Monodicity Causes Undecidability").
