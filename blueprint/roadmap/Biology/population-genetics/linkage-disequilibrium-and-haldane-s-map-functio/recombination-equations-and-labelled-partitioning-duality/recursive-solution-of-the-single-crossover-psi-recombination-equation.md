# Recursive solution of the single-crossover $\psi$-recombination equation

Consider the [$\psi$-recombination equation](labelled-partitioning-process-dual-to-the-psi-recombination-equation.md) on sites $S = \{1,\dots,n\}$ with active site $i_\bullet$ and **single-crossover** recombination only. Order sites by distance from the active site: $i \preccurlyeq j$ iff $i_\bullet \le i \le j$ or $j \le i \le i_\bullet$. For $i \ne i_\bullet$ let $D_i = \{j : i \preccurlyeq j\}$ (the $i$-tail, the sites at least as far from $i_\bullet$ as $i$, on its side) and $C_i = S \setminus D_i$ (the $i$-head, containing $i_\bullet$); explicitly $(C_i,D_i) = ([1,i-1],[i,n])$ if $i > i_\bullet$ and $([i+1,n],[1,i])$ if $i < i_\bullet$. With $\varrho_i \ge 0$ the crossover rate at $i$, the equation reads

$$\dot\omega_t = \psi(\omega_t) + \sum_{i \ne i_\bullet} \varrho_i\bigl(\omega_{C_i,t}\otimes\omega_{D_i,t} - \omega_t\bigr),$$

with $\psi$ satisfying the head-only multiplicativity and marginal-affinity assumptions.

Fix an enumeration $i^{(0)} = i_\bullet, i^{(1)}, \dots, i^{(n-1)}$ of $S$ that is nondecreasing for $\preccurlyeq$, write $\varrho^{(k)}, C^{(k)}, D^{(k)}$ for $\varrho_{i^{(k)}}, C_{i^{(k)}}, D_{i^{(k)}}$, and let $\omega^{(k)}$ solve the equation **truncated at $k$**,

$$\dot\omega^{(k)}_t = \psi(\omega^{(k)}_t) + \sum_{\ell=1}^{k}\varrho^{(\ell)}\bigl(\omega^{(k)}_{C^{(\ell)},t}\otimes\omega^{(k)}_{D^{(\ell)},t} - \omega^{(k)}_t\bigr), \qquad \omega^{(k)}_0 = \omega_0 .$$

**Theorem.** For $1 \le k \le n-1$,

$$\omega^{(k)}_t = e^{-\varrho^{(k)} t}\,\omega^{(k-1)}_t + \omega^{(k-1)}_{C^{(k)},t}\otimes\int_0^t \varrho^{(k)} e^{-\varrho^{(k)}\tau}\,\omega^{(k-1)}_{D^{(k)},\tau}\,d\tau,$$

starting from the solution $\omega^{(0)}$ of $\dot\omega^{(0)}_t = \psi(\omega^{(0)}_t)$. Hence $\omega_t = \omega^{(n-1)}_t$ is obtained from the recombination-free flow by $n-1$ explicit steps.

In the single-crossover case the labelled partitioning process reduces to independent site-wise processes: the active site carries a copy of the dual $Y$, and each other site $i$ carries either a block-structure marker $\Delta$ (left at rate $\varrho_i$, jumping to the empty genealogy) or a copy of $Y$ that is reset to the empty genealogy at rate $r_i = \sum_{j \preccurlyeq i,\, j\ne i_\bullet}\varrho_j$.

## Depends on

- [Labelled partitioning process dual to the $\psi$-recombination equation](labelled-partitioning-process-dual-to-the-psi-recombination-equation.md)

## Expansion

For two sites with $i_\bullet = 1$, the dual is: the two sites are split at rate $\varrho^{(1)}$, after which the label of site 2 is frozen and site 1 keeps a running clock. With $T$ the time since the last crossover event, exponential with rate $\varrho^{(1)}$, the duality gives $\omega_t = \mathbb{E}[\mathbf{1}_{T\ge t}\,\omega^{(0)}_t + \mathbf{1}_{T<t}\,\omega^{(0)}_{\{1\},t}\otimes\omega^{(0)}_{\{2\},T}]$, which is the formula for $k=1$. The general step is a reduction to two "super-sites" $C^{(k)}$ and $D^{(k)}$ with the modified vector field $\tilde\psi = \psi + \sum_{\ell<k}\varrho^{(\ell)}(\nu_{C^{(\ell)}}\otimes\nu_{D^{(\ell)}} - \nu)$; the monotone enumeration guarantees $C^{(\ell)}\subseteq C^{(k)}$ or $D^{(\ell)}\subseteq C^{(k)}$ for $\ell<k$, so $\tilde\psi$ still acts only through the head $C^{(k)}$ and satisfies the assumptions. This unifies the known recursion for the selection-recombination equation (where $\psi$ is frequency-independent selection at $i_\bullet$) and extends it to selection plus mutation at the selected site.

## Sources

- Frederic Alberti, "Labeled partitions in action: Recombination, selection, mutation and more", *Stochastics and Dynamics* 24 (2024), 2450014, <https://doi.org/10.1142/s021949372450014x>. Numbering as in the preprint arXiv:2203.10874v2, <https://arxiv.org/abs/2203.10874v2>: Section 4: Definitions 4.1–4.2, Lemma 4.3, Proposition 4.5, Theorem 4.6; application to selection-mutation-recombination in Section 5.
