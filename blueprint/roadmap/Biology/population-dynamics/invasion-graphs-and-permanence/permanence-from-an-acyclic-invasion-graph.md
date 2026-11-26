# Permanence from an acyclic invasion graph

**Setting.** Let $\dot x_i = x_i f_i(z)$, $\dot y = g(z)$ be an ecological model on
$K = [0, \infty)^n \times Y$ satisfying the standing assumptions A1 (local Lipschitz), A2
(dissipativity) and A3 (nonzero invasion growth rates of missing species, with signs determined by
the species support), and let $r_i(S) \in \{-1, 0, +1\}$ and the invasion graph on the set
$\mathcal{S}$ of proper subcommunities be as in the definition of the invasion graph. The system is
**permanent** if there is a compact set in $K \setminus K_0$ that every trajectory starting in
$K \setminus K_0$ eventually enters, and **robustly permanent** if it stays permanent under small
perturbations of $f$ and $g$.

**Theorem.** If the invasion graph is acyclic and every subcommunity is invadable, i.e. for every
$S \in \mathcal{S}$ some species $i$ has $r_i(S) > 0$, then the system is robustly permanent.

**Corollary 1 ($-i$ communities).** Call $S \subseteq [n] \setminus \{i\}$ a $-i$ community if
$r_j(S) \le 0$ for all $j \ne i$. If the invasion graph is acyclic and $r_i(S) > 0$ for every $-i$
community $S$ and every $i \in [n]$, the system is robustly permanent.

**Corollary 2 (sequential permanence).** The invasion scheme is sequentially permanent if the species
can be ordered $\ell_1, \dots, \ell_n$ so that, with $IS_1$ the full scheme and $IS_k$ obtained from
$IS_{k-1}$ by deleting the rows in which $\ell_{k-1}$ has positive growth rate, column $\ell_k$ of
$IS_k$ has only nonnegative entries. A sequentially permanent scheme yields robust permanence.

**Proposition (sign-robust average Lyapunov function).** An invasion scheme is sequentially permanent
if and only if every matrix $C$ with $\operatorname{sgn} C$ equal to the scheme admits $p \gg 0$ with
$C p \gg 0$, that is, Hofbauer's average Lyapunov condition $\sum_i p_i r_i(\mu) > 0$ holds for every
choice of magnitudes compatible with the signs.

## Depends on

- [Invasion graph of an ecological community](invasion-graph-of-an-ecological-community.md)

## Expansion

Acyclicity of the invasion graph lets one order the subcommunities and build a Morse decomposition
of the flow on the extinction set $K_0$, with one Morse set per subcommunity. Invadability of each
subcommunity means that some species grows when rare near the corresponding Morse set, so its
stable set does not meet the interior $K \setminus K_0$; by the Morse-decomposition criterion for
permanence (Garay and Hofbauer), the boundary is then a repeller, which is permanence, and the strict
sign conditions persist under small perturbations. Without acyclicity, signs alone do not decide:
three competitors with a heteroclinic cycle (rock–paper–scissors) can have every subcommunity
invadable yet fail to be permanent, depending on the magnitudes of the invasion growth rates. If
instead some subcommunity has all missing species with negative invasion growth rates and the
vector field is $C^2$, Pesin's stable manifold theorem gives interior trajectories converging to the
boundary, so the system is not permanent. Corollary 1 reduces the check to the communities that a
species $i$ actually faces after its own extinction, matching the "mutual invasibility" criterion
of modern coexistence theory.

## Sources

- J. Hofbauer, S. J. Schreiber, "Permanence via invasion graphs: incorporating community assembly
  into modern coexistence theory", Journal of Mathematical Biology 85 (2022) 54, Theorem 1, Remark 3,
  Corollaries 1-2, condition H and the sequential-permanence proposition,
  <https://doi.org/10.1007/s00285-022-01815-2> (PMC9579112).
