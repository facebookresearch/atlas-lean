# Fast TBR and SPR neighbourhood search for RF supertrees

Let $\mathcal P = (T_1, \dots, T_k)$ be a profile of rooted trees and $T$ a rooted binary supertree with $n$ leaves. For an edge $(u, v)$ with $u = \mathrm{pa}(v)$, deleting it splits $T$ into the pruned subtree $X \ni v$ and the remainder $Y \ni u$. The **TBR** move $\mathrm{TBR}_T(v, x, y)$ reroots $X$ at $x \in V(X)$ and regrafts it onto the edge above $y \in V(Y)$; the **SPR** move $\mathrm{SPR}_T(v, y) = \mathrm{TBR}_T(v, v, y)$ keeps the root of $X$. Write $\mathrm{TBR}_T(v)$ for all moves pruning at $v$, and $\mathrm{TBR}_T$ for all moves; $|\mathrm{TBR}_T| = \Theta(n^3)$.

**Problems.** *TBR-RS*: given $(\mathcal P, T, v)$, find $T^* \in \mathrm{TBR}_T(v)$ minimizing $\mathrm{RF}(\mathcal P, \cdot)$. *TBR-S*: find a minimizer over all of $\mathrm{TBR}_T$. *Rooting*: find $x \in V(T_v)$ minimizing $\mathrm{RF}(\mathcal P, \mathrm{TBR}_T(v, x, y))$ with $y$ the sibling of $v$. SPR-RS and SPR-S are defined analogously.

**Lemma (decomposition).** For one input tree $S$, partition $I(S)$ into $X_S = \{u : \mathcal M_{S,T}(u) \in V(T_v)\}$ and its complement. Nodes in $X_S$ keep their indicator $f$ under every regraft that does not reroot, and nodes outside $X_S$ keep it under every rerooting regrafted at the original position. Hence an optimal TBR move pruning at $v$ combines an optimal rooting of $T_v$ with an optimal SPR regraft position, chosen independently.

**Theorems.** Rooting and SPR-RS can each be solved in $O(kn)$ time; hence TBR-RS is solvable in $O(kn)$ time and TBR-S (and so SPR-S) in $O(kn^2)$ time.

## Depends on

- [Robinson–Foulds distance via the LCA mapping](robinson-foulds-distance-via-the-lca-mapping.md)

## Expansion

By the LCA-mapping identity, minimizing $\mathrm{RF}$ over a neighbourhood amounts to minimizing the number of input clusters missing from the candidate tree, and a cluster is present exactly when its LCA image has the right leaf count. The decomposition reduces the $O(n^2)$ (rooting, regraft) pairs per pruned edge to $O(n)$ candidates. Case analyses on where the LCA image of each input node falls relative to the moved subtree (Lemmas 4–12) show how $f$ changes as the root of $T_v$ or the regraft point moves one edge, allowing all candidates to be scored in one traversal per input tree. Over the $|E(T)| = O(n)$ prune edges this gives $O(kn^2)$, versus $O(kn^3)$ and $O(kn^4)$ for naive SPR and TBR searches; after preprocessing, the RF distance of any tree in $\mathrm{TBR}_T$ is available in $O(1)$ time. Input trees may be non-binary.

## Sources

- M. S. Bansal, J. G. Burleigh, O. Eulenstein, D. Fernández-Baca, "Robinson-Foulds supertrees", Algorithms for Molecular Biology 5 (2010) 18, Definitions 2–5, Problems 2–4, Lemma 3, Theorems 1–4, <https://doi.org/10.1186/1748-7188-5-18>, PMCID PMC2846952.
