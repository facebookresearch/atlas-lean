# Matching-minus-discordant internal branch length of a quartet

**Model (MSC with substitution rates).** Each branch $i$ of a rooted species tree has a length $\tau_i$ in generations, a haploid effective size $N_i$ and a per-generation substitution rate $\nu_i$. Its coalescent-unit (CU) length is $T_i = \tau_i / N_i$, its CU substitution rate is $\mu_i = \nu_i N_i$, and its substitution-unit (SU) length is $t_i = \mu_i T_i$. Gene trees are drawn from the multispecies coalescent in CU time, and every infinitesimal piece of a gene-tree branch lying in species branch $i$ is then scaled by $\mu_i$, giving non-ultrametric gene trees in SU.

**Quartet.** Take the unbalanced rooted species tree $(((A, B), C), D)$ on four taxa. Its focal internal branch $1$ (CU length $T_1$, rate $\mu_1$) is the stem of the cherry $(A, B)$; branch $2$ (CU length $T_2$, rate $\mu_2$) is the stem of $((A, B), C)$; and $\mu_3$ is the rate of the next species-tree branch above, so $\mu_2, \mu_3$ are the rates of the two branches above the focal one. Let $\Delta_I$ be the expected SU length of the internal branch of gene trees whose unrooted topology matches the species quartet $AB|CD$, minus the expected internal length of gene trees with a discordant unrooted topology.

**Theorem.**

$$\Delta_I = \frac{3\bigl(e^{-T_2} - e^{-3T_2}\bigr)\bigl(1 - e^{-T_1}\bigr)(\mu_2 - \mu_3) + 6\mu_1\bigl(e^{-T_1} - 1 + T_1\bigr)}{2\bigl(3 - 2e^{-T_1}\bigr)} .$$

In particular, in each of the limits $T_2 \to \infty$, $T_2 \to 0$ and $\mu_2 \to \mu_3$,

$$\Delta_I = \frac{3\mu_1\bigl(T_1 + e^{-T_1} - 1\bigr)}{3 - 2e^{-T_1}},$$

which depends only on the focal branch.

**Estimator.** Under a local clock ($\mu_2 = \mu_3 = \mu_1$) the expected internal length of discordant gene trees equals $\mu_1$, so with $\bar\Delta_I$ the observed matching-minus-discordant difference and $\bar L_I'$ the observed mean internal length of discordant gene trees, $\bar\delta = \bar\Delta_I / \bar L_I'$ satisfies

$$\bar\delta = \frac{3\bigl(T_1 + e^{-T_1} - 1\bigr)}{3 - 2e^{-T_1}} .$$

Replacing $e^{-T_1}$ by $1/(1 + T_1)$ turns this into $\bar\delta (1 + 3T_1) = 3T_1^2$, whose positive root is

$$\hat T_1 = \frac{\bar\delta}{2} + \frac{1}{6}\sqrt{3\bar\delta(3\bar\delta + 4)},$$

and the SU length estimate is $\hat t_1 = \bar L_I' \, \hat T_1$ (set to a small positive value when $\bar\delta < 0$).

## Depends on

- [The multispecies coalescent](../../../coalescent-theory/multispecies-coalescent/gene-tree-prob.md)

## Expansion

In a matching gene tree the internal branch includes the part of branch $1$ during which the $A$ and $B$ lineages have coalesced but neither has met $C$ or $D$, plus a contribution from deeper coalescences; in a discordant gene tree the internal branch arises only from coalescence above branch $1$, so differencing cancels most of the deep-time contribution and leaves the term $6\mu_1(e^{-T_1} - 1 + T_1)$, the expected excess time spent in branch $1$. The probability $1 - \tfrac23 e^{-T_1}$ of a matching topology produces the denominator $3 - 2e^{-T_1}$. The exact equation is solvable with the Lambert $W$ function; the substitution $e^{T_1} \approx 1 + T_1$ is accurate for short branches, where discordance is common and the estimator matters most. For trees with $n > 4$ taxa, each internal branch defines four leaf groups, the quartet quantities are averaged over all quartets with one leaf in each group, and these averages over all $\Theta(n^4)$ quartets are computed by dynamic programming in $O(n^2)$ time per gene tree.

## Sources

- Y. Tabatabaee, C. Zhang, T. Warnow, S. Mirarab, "Phylogenomic branch length estimation using quartets", Bioinformatics 39 (Supplement 1) (2023) i185–i193, Sections 2.1–2.3, Theorem 1 and Equations (1), (5)–(7), <https://doi.org/10.1093/bioinformatics/btad221> (PMC10311336).
