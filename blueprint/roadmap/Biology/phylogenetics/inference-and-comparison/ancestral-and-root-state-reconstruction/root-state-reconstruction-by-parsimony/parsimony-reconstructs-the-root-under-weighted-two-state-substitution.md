# Parsimony reconstructs the root state under heterogeneous two-state substitution

**Setting.** Let $T$ be the infinite complete binary tree rooted at $\rho$, with edge weights $\theta_z \in [0,1]$ indexed by the lower endpoint $z$ of each edge. Under the **Cavender–Farris–Neyman model**, $\sigma_\rho$ is uniform on $\{0,1\}$ and, recursively, a child copies its parent's state with probability $\theta_z$ and is otherwise resampled uniformly, so the substitution probability on edge $z$ is $p_z = (1-\theta_z)/2$. A **cutset** $\pi$ is a minimal finite vertex set meeting every infinite path from $\rho$. Given the states on $\pi$, the [Fitch recursion](../../../small-parsimony-problem/fitch-set-eq.md) produces the maximum parsimony root estimate $\hat\sigma_\rho$ (uniform tie-breaking), and its **reconstruction accuracy** is $\mathrm{RA}^\pi = \mathbb P[\hat\sigma_\rho = \sigma_\rho]$. Parsimony is said to reconstruct the root if $\inf_\pi \mathrm{RA}^\pi > 1/2$.

**Theorem (deterministic weights, Theorem 1).** Suppose $\theta_* := \inf_z \theta_z > 0$ and

$$\sup\Big\{\kappa > 0 : \inf_{\pi} \sum_{x \in \pi} \prod_{\rho \ne z \le x} \kappa^{-1}\theta_z > 0\Big\} > \frac{3}{2}.$$

Then $\inf_\pi \mathrm{RA}^\pi > 1/2$. In particular (Corollary 1), if $p_z \le p_* < 1/8$ for every edge, parsimony reconstructs the root.

**Theorem (random weights, Theorem 2).** If the $\theta_z$ are i.i.d. from a distribution on $(0,1]$ with mean $\mu > 3/4$, then for every $\delta > 0$ there is $\varepsilon > 0$ with $\inf_\pi \mathrm{RA}^\pi > \frac12(1+\varepsilon)$ with probability at least $1-\delta$.

## Depends on

- [Fitch's root set is the set of optimal root states](../../../small-parsimony-problem/fitch-set-eq.md)

## Expansion

The left side of the branching condition is a weighted branching number of the tree. For constant weights $\theta$ it equals $2\theta$, so the condition becomes $\theta > 3/4$, i.e. $p < 1/8$, which is the classical threshold for parsimony on the homogeneous binary tree; the theorem says that the same threshold, read as a weighted branching number, controls heterogeneous trees. The proof tracks two quantities along the Fitch recursion: the bias $G_z$ of the Fitch set toward the true state and a second recursively defined quantity $F_z \in [-1/2, 1]$ (Proposition 1). A cutset expansion of $G_\rho$ through products of factors $\frac{4 - F_{s(z)}}{6}\theta_z$ (Lemma 1) turns the problem into a branching-number estimate, with $\frac{2}{3}$ coming from the regime where $F$ is near zero. In the i.i.d. case, the edges with large weights form a supercritical Galton–Watson subtree whose weighted branching number is $2\tilde q\tilde\mu$ (Lemma 4), so a mean above $3/4$ suffices.

## Sources

- Sebastien Roch and Kun-Chieh Wang, "Sufficient condition for root reconstruction by parsimony on binary trees with general weights", arXiv:1708.02524 (2017), Section 2 (model, Definitions 1–2), Theorems 1–2, Example 1, Corollary 1, Lemmas 1 and 4, <https://doi.org/10.48550/arXiv.1708.02524>. Published version: Electronic Communications in Probability 26 (2021) 1–13, <https://doi.org/10.1214/21-ecp423>.
