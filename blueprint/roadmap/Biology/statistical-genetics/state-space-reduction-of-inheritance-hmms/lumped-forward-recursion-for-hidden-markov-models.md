# Lumped forward recursion for hidden Markov models

Let $(S_i, X_i)_{i=1}^L$ be a hidden Markov model with finite hidden state space $\mathcal S$, initial law $P(s_1)$, transitions $P(s_i \mid s_{i-1})$ and emissions $P(x_i \mid s_i)$, so that
$$P(x_1,\dots,x_L) = \sum_{s_1,\dots,s_L} P(s_1)\prod_{i=2}^L P(s_i\mid s_{i-1})\prod_{i=1}^L P(x_i\mid s_i).$$
Let $\sim$ be a partition of $\mathcal S$ into classes $[s]$, and write $P([s]\mid s') = \sum_{t \in [s]} P(t\mid s')$.

**Condition I.** $P(x_i \mid s) = P(x_i\mid s')$ whenever $s \sim s'$.

**Condition II.** $P([s]\mid s') = P([s]\mid s'')$ whenever $s' \sim s''$.

**Theorem (lumped likelihood).** Under Conditions I and II, with $P(x_i\mid[s]) := P(x_i\mid s)$, $P([s]\mid[s']) := P([s]\mid s')$ and $P([s_1]) := \sum_{t\in[s_1]}P(t)$,
$$P(x_1,\dots,x_L) = \sum_{[s_1],\dots,[s_L]} P([s_1])\prod_{i=2}^L P([s_i]\mid[s_{i-1}])\prod_{i=1}^L P(x_i\mid[s_i]),$$
so the forward algorithm can run on the quotient state space.

**Theorem (counting partition).** In a homogeneously factored HMM whose hidden state is a vector of $k$ binary *selectors*, each flipping independently between consecutive slots with probability $\theta$, group the selectors into disjoint clusters $C_1,\dots,C_m$ of sizes $r_1,\dots,r_m$, and call two states of a cluster equivalent when they have the same number of selectors on. The product partition on $[C_1]\times\cdots\times[C_m]$ satisfies Condition II. For one cluster of $r$ selectors, the probability of moving from a state with $j$ selectors on to the class of states with $i$ on is
$$\sum_{t} \binom{j}{t}\binom{r-j}{i-t}\,\theta^{\,i+j-2t}(1-\theta)^{\,r-i-j+2t},$$
which depends only on $j$. Each cluster then has $r+1$ instead of $2^r$ states.

## Depends on

- [Lander–Green multipoint pedigree likelihood](../lander-green-multipoint-pedigree-likelihood/README.md)

## Expansion

Condition I lets the innermost emission factor be pulled out of the sum over each class, and Condition II lets the remaining sum over the class members be written as a class-to-class transition probability; repeating over $L, L-1, \dots, 1$ turns the full sum into the lumped one. For the counting partition, a transition from a state with $j$ selectors on to a fixed state with $i$ on, sharing $t$ on-selectors, needs $(j-t) + (i-t)$ flips among $r$ selectors; summing over the $\binom{j}{t}\binom{r-j}{i-t}$ target states with each overlap $t$ gives a value independent of which $j$ selectors were on. With $k$ selectors split into $m$ equal clusters, each with $d = 1 + k/m$ states, one forward step costs $O(m\,d^{m+1})$ operations instead of exponential in $k$.

## Sources

- D. Geiger, C. Meek, Y. Wexler, "Speeding up HMM algorithms for genetic linkage analysis via chain reductions of the state space", Bioinformatics (2009), Sects. 2–3, Conditions I–II, Eqs. (1)–(4), Theorem 1, <https://doi.org/10.1093/bioinformatics/btp224>, PMCID PMC2687978.
