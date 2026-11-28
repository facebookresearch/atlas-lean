# Suffix support bound for repeated structured motifs

**Setting.** A structured motif is

$$\mathcal M = M_1[l_1, u_1]\,M_2[l_2, u_2]\cdots M_{k-1}[l_{k-1}, u_{k-1}]\,M_k,$$

where the $M_i$ are simple motif components (short strings over $\{A,C,G,T\}$, possibly matched with a bounded number of substitutions) and $0 \le l_i \le u_i$ are the minimum and maximum gap lengths between $M_i$ and $M_{i+1}$: if $M_i$ ends at $e_i$ and $M_{i+1}$ starts at $s_{i+1}$, the gap $g_i = s_{i+1} - e_i - 1$ must lie in $[l_i, u_i]$. An occurrence of $\mathcal M$ in a sequence set is a choice of positions of all components satisfying the gap constraints; the **weighted support** $\pi_w(\mathcal M) = |\mathcal O(\mathcal M)|$ counts all occurrences (including repeated ones in the same sequence). Write $W_m = u_m - l_m + 1$ for the span of the $m$-th gap range.

In the repeated-motif problem the downward closure property fails: in GCTTT the pattern G[1,3]T occurs three times while its sub-pattern G occurs once.

**Theorem.** For a structured motif $\mathcal M = M_1\cdots M_k$ and its suffix $\mathcal M' = M_i\cdots M_k$ ($1 \le i \le k$, with the same gaps),

$$\pi_w(\mathcal M') \ge \frac{\pi_w(\mathcal M)}{\prod_{m=1}^{i-1} W_m}.$$

Consequently, if $\mathcal M$ must reach a quorum of $q$ occurrences, every suffix $\mathcal M'$ that can be extended to such an $\mathcal M$ must have $\pi_w(\mathcal M') \ge q / \prod_{m=1}^{i-1}W_m$, and suffixes below this bound can be pruned.

## Expansion

Every occurrence of $\mathcal M$ restricts to an occurrence of the suffix $\mathcal M'$, and conversely one occurrence of $\mathcal M'$ extends to at most $\prod_{m<i} W_m$ occurrences of $\mathcal M$, since once $M_i$ is fixed each preceding component $M_m$ has at most $W_m$ admissible end positions determined by the gap range (for exact components). Hence $|\mathcal O(\mathcal M')|\prod_{m<i}W_m \ge |\mathcal O(\mathcal M)|$. For the template NN[3,5]NNN[0,4]NNN with quorum $q = 100$, $W_1 = 3$ and $W_2 = 5$, so the last component must occur at least $\lceil 100/15 \rceil = 7$ times. EXMOTIF combines this bound with bit-vector occurrence lists on a suffix tree to extract structured motifs from right to left, and then scores each frequent motif with an information-content-weighted position weight matrix, $W^c_{ij} = \mathcal I_j \ln(r_{ij}/p_i)$.

## Sources

- Y. Zhang, M. J. Zaki, "EXMOTIF: efficient structured motif extraction", Algorithms for Molecular Biology 1 (2006) 21, structured motif definition, Eqs. (1)–(3) and Theorem 1 with its proof and example, <https://doi.org/10.1186/1748-7188-1-21>, PMCID PMC1698483.
