# Limit laws for fringe patterns in ranked tree-child networks

**Definitions.** A phylogenetic network is **tree-child** if every non-leaf node has at least one child that is not a reticulation node. It is **rankable** if it can be grown from a single branching event by attaching, in each step, either a branching event (one lineage splits) or a reticulation event (a reticulation node with its two parents: each of two lineages continues through a new tree node, the other children of these two tree nodes meet at a new reticulation node, and that node has one child lineage, so two lineages become three) at the leaves; a rankable network together with such an ordering of its events is a **ranked tree-child network**. A pattern of height $h$ is a fringe configuration created by $h$ consecutive events; the height-$1$ patterns are **cherries** (from a branching event) and **tridents** (from a reticulation event). Let $C_n$, $T_n$ be their numbers in a ranked tree-child network chosen uniformly among those with $n$ leaves.

**Markov chain representation.** $T_n$ has the law of the Markov chain with $T_2 = 0$ and, given $T_n = j$, $T_{n+1} = j - 1$ with probability $3j(3j-2)/n^2$, $j + 1$ with probability $(n - 3j)(n - 3j - 1)/n^2$, and $j$ otherwise. Its mean satisfies $\mu_{n+1} = (1 - 3/n)^2\mu_n + 1 - 1/n$, so

$$\mathbb{E}(T_n) = \frac{(15n^3 - 85n^2 + 144n - 71)\,n}{105(n-1)(n-2)(n-3)}, \qquad n \ge 4 .$$

**Theorem (tridents).** As $n \to \infty$,

$$\frac{T_n - n/7}{\sqrt{24n/637}} \xrightarrow{d} \mathcal{N}(0,1),$$

with all central moments converging: $\mathbb{E}\big((T_n - \mu_n)^m\big) \sim g_m (24/637)^{m/2} n^{m/2}$, $g_m$ the standard normal moments. (Cherries, by contrast, converge to $\mathrm{Poisson}(1/4)$.)

**Theorem (height-2 patterns).** For the number $X_n$ of occurrences of a fixed height-$2$ pattern, exactly one of three behaviours occurs: (A) degenerate, $X_n \to 0$ in $L_1$; (B) Poisson, $X_n \xrightarrow{d} \mathrm{Poisson}(\lambda)$ with $\lambda \in \{1/8, 1/28, 1/56, 1/14, 1/28\}$ for the five Poisson-type patterns; for the pattern of the source's Figure 3-(b-i) (limit $\mathrm{Poisson}(1/8)$), jointly with $C_n$, $(X_n, C_n)$ converges to independent Poisson variables with parameters $1/8$ and $1/4$ (Proposition 2(b)); (C) normal, $(X_n - \mu n)/(\sigma\sqrt n) \xrightarrow{d} \mathcal{N}(0,1)$ with $(\mu,\sigma^2) = (4/77,\ 4575916/137582445)$ or $(2/77,\ 2930764/137582445)$ for the two normal-type patterns.

## Expansion

Growing the network one leaf at a time, a uniformly random ranked tree-child network with $n + 1$ leaves arises from one with $n$ leaves by choosing the next event uniformly, which turns pattern counts into Markov chains whose transition probabilities depend only on the current counts. Each pattern occurrence is destroyed when one of its leaves is involved in the next event, which happens with probability about $2\cdot(\text{number of leaves in the pattern})/n$, giving the recurrences $\phi_{n+1} = (1 - c/n)^2\phi_n + \psi_n$ for moments. A transfer lemma ($\psi_n \sim c n^\alpha$ implies $\phi_n \sim c\,n^{\alpha+1}/(2\kappa + \alpha + 1)$) converts these into asymptotics: patterns whose predecessor occurs linearly often are created at constant rate and are Poisson, those created from Poisson patterns vanish, and those created from linear-frequency patterns are themselves linear with Gaussian fluctuations.

## Sources

- Michael Fuchs, Hexuan Liu, Tsan‐Cheng Yu, "Limit theorems for patterns in ranked tree‐child networks", Random Structures & Algorithms 64 (2024), 15–37, <https://doi.org/10.1002/rsa.21177>. Published version of arXiv:2204.07676, cited next; locators there refer to the arXiv version.
- Michael Fuchs, Hexuan Liu, Tsan-Cheng Yu, "Limit Theorems for Patterns in Ranked Tree-Child Networks", arXiv (2022). Definitions 1–2, Theorem 1, Theorem 2, Lemmas 1–4, Proposition 1, Propositions 2–3. <https://doi.org/10.48550/arXiv.2204.07676>
