# First-order tautologies of infinite NM-chains are not recursively enumerable

For every countable complete subalgebra of the nilpotent minimum algebra on $[0,1]$, the set of first-order tautologies is not recursively enumerable, and for most infinite complete subalgebras even the monadic tautologies are undecidable; in contrast, finite NM-chains have recursively axiomatizable first-order logics.

**Theorem (Bianchi).** For the [first-order nilpotent minimum logics](first-order-nilpotent-minimum-logic.md):

1. If $\mathcal{A}$ is a countable topologically closed (equivalently, countable complete) subalgebra of $[0,1]_{\mathrm{NM}}$, then $\mathrm{TAUT}_{\mathcal{A}}\forall$ is not recursively enumerable (Theorem 18). In particular this holds for $\mathcal{A} \in \{NM_\infty, NM_\infty^-, NM'_\infty\}$ (Corollary 6).
2. If $\mathcal{A}$ is an infinite complete subalgebra of $[0,1]_{\mathrm{NM}}$ other than $NM_\infty$ and $NM_\infty^-$, then $\mathrm{monTAUT}_{\mathcal{A}}\forall$ is undecidable (Theorem 21); in particular $\mathrm{monTAUT}_{NM'_\infty}\forall$ is undecidable (Corollary 7).

For finite NM-chains, the first-order tautologies are recursively axiomatizable (Theorem 14) and the monadic ones are decidable (Theorem 19). The cases $NM_\infty$ and $NM_\infty^-$ in clause 2, and the arithmetical complexity of $\mathrm{TAUT}_{NM'^-_\infty}\forall$, are left open by the source.

## Depends on

- [First-order nilpotent minimum logic over NM-chains](first-order-nilpotent-minimum-logic.md)
- [Complete lattice](../../../Order/lattices-boolean-algebras/complete-lattice.md)

## Proof depends on

None.

## Expansion

The proof transfers results on first-order Gödel logics, whose truth values form a Gödel chain with $x * y = \min(x,y)$: by results cited in the source (Theorems 17 and 20), the first-order tautologies of a countable complete subalgebra of $[0,1]_{\mathrm{G}}$ are not recursively enumerable, and the monadic tautologies of an infinite complete subalgebra of $[0,1]_{\mathrm{G}}$ other than $G_\uparrow$ are undecidable. A "connected rotation" turns a Gödel chain $\mathcal{B}$ into an NM-chain $\mathcal{B}_{\mathrm{NM}}$ with a negation fixpoint, and the translation $\varphi \mapsto \varphi^*$, which squares atoms, implications and universal formulas, satisfies $\mathcal{B} \models \varphi$ iff $\mathcal{B}_{\mathrm{NM}} \models \varphi^*$ (Corollary 5). A complete subalgebra of $[0,1]_{\mathrm{NM}}$ with a fixpoint is of the form $\mathcal{B}_{\mathrm{NM}}$; a chain without fixpoint is handled by adding one (Theorem 15). $G_\uparrow$ corresponds to $NM_\infty$, which explains the exception in clause 2.

## Sources

- M. Bianchi, "First-order nilpotent minimum logics: first steps", *Archive for Mathematical Logic* 52(3–4):295–316, 2013, doi:10.1007/s00153-012-0317-4; read as arXiv:1103.6025v2, <https://arxiv.org/abs/1103.6025v2>: Theorems 14, 15, 18, 19 and 21, Corollaries 5, 6 and 7, Definitions 1 and 2, Remark 2, Theorems 17 and 20, and Section 3.1 of arXiv:1103.6025v2.
