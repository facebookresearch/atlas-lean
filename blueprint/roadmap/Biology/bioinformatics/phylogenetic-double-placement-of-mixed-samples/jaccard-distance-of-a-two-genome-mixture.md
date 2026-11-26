# Jaccard distance of a two-genome mixture

**Setting.** Genomes are modelled as sets of $n$ distinct k-mers. For two genomes at per-site distance $\delta$ (proportion of differing sites), a k-mer is shared iff none of its $k$ positions changed, so $|S_A \cap S_R| \approx n(1-\delta)^k$, and the Jaccard index $J_{AR} = |S_A \cap S_R|/|S_A \cup S_R|$ yields the estimator

$$\hat\delta_{AR} = 1 - \Big(\frac{2J_{AR}}{1 + J_{AR}}\Big)^{1/k}.$$

A mixed sample $M$ contains the k-mers of two genomes $A$ and $B$. Let $d_1, d_2, d_3$ be the evolutionary distances (substitutions per site) from a reference genome $R$ to $A$, from $R$ to $B$, and from $A$ to $B$, with $\delta = h(d)$ the Jukes–Cantor proportion $h(d) = \tfrac34(1 - e^{-4d/3})$, and let the three genomes meet at an ancestral point $L$ (distance $(d_1 + d_3 - d_2)/2$ from $A$, and so on). Define the mixture distance $\hat\delta_{MR} = 1 - \big(2J_{MR}/(1 + J_{MR})\big)^{1/k}$, computed from the observable $J_{MR}$.

**Model.** By inclusion–exclusion on $S_A \cup S_B$ and $S_R$, and approximating the triple intersection by $n\big(1 - h(\tfrac{d_1 + d_2 + d_3}{2})\big)^k$,

$$\hat\delta_{MR} = 1 - \left(\frac{2\big[(1-h(d_1))^k + (1-h(d_2))^k - (1 - h(\tfrac{d_1+d_2+d_3}{2}))^k\big]}{3 - (1 - h(d_3))^k}\right)^{1/k}.$$

**Proposition.**
1. (Bounds) If $\delta_{AR} \le \delta_{BR}$ and $z = \hat\delta_{MR}$, then $\delta_{AR} \ge 1 - (3/2)^{1/k}(1 - z)$, and $\delta_{AR} \le u$ where $u$ solves $\dfrac{4(1-u)^k - 2(1-2u)^k}{3 - (1-2u)^k} = (1-z)^k$: the mixture distance is controlled by the distance to the closer constituent, close to $\min(\delta_{AR}, \delta_{BR})$ rather than to their mean.
2. (Known constituent) If $A$ is a reference and $B$ is not, the reference minimizing $\hat\delta_{MR_i}$ is $A$, and

$$\hat\delta_{MA} = 1 - \Big(\frac{2}{3 - (1-\delta_3)^k}\Big)^{1/k}.$$

3. (Both known) If both $A$ and $B$ are references, they are the two references with smallest $\hat\delta_{MR_i}$, and both values equal the expression in part 2, which is bounded above independently of $\delta_3$ by $1 - \big(2/(3 - 4^{-k})\big)^{1/k}$ (about $0.013$ for $k = 31$).

## Expansion

The Jaccard index of the mixture is $J_{MR} = \frac{|S_A\cap S_R| + |S_B\cap S_R| - |S_A\cap S_B\cap S_R|}{3n - |S_A\cap S_R| - |S_B\cap S_R| - |S_A\cap S_B| + |S_A\cap S_B\cap S_R|}$; substituting the expected intersection sizes gives the model. Setting $d_1 = 0$ (so $\delta_2 = \delta_3$) collapses $J_{MR}$ to $1/(2 - (1-\delta_3)^k)$, from which part 2 follows directly, and $\delta_3 \le 3/4$ gives the uniform bound in part 3. Part 1 follows by bounding the triple-intersection term between its extremes under the triangle inequality. A single $\hat\delta_{MR}$ cannot identify $(d_1, d_2, d_3)$, but many references on a known tree impose triangle inequalities and near-additivity; the double-placement method chooses two placement edges and pendant lengths minimizing least-squares deviation from additivity subject to the bounds of part 1, which places both unknown constituents of a mixture on the reference phylogeny.

## Sources

- M. Balaban, S. Mirarab, "Phylogenetic double placement of mixed samples", Bioinformatics 36 (Suppl. 1) (2020) i335–i343, Eqs. (1)–(4), Propositions 1–2 and Corollary 3 (proofs in Appendix 1), Section 2.2, <https://doi.org/10.1093/bioinformatics/btaa489>, PMCID PMC7355250.
