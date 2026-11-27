# Uninhibited RAFs by enumeration of inhibitor subsets

**Setting.** A CRS with inhibition is $Q = (X, \mathcal R, C, I, F)$, where $(X, \mathcal R, C, F)$ is a catalytic reaction system as in [pseudo-RAF theory](pseudo-raf-sets-and-the-alternating-maxraf-algorithm.md) and $(x, r) \in I$ means that molecule $x$ inhibits reaction $r$. A **u-RAF** is an RAF $\mathcal R'$ such that no reaction of $\mathcal R'$ is inhibited by a molecule of $\mathrm{cl}_{\mathcal R'}(F)$. Assume without loss of generality that no reaction is inhibited by a food molecule (such reactions lie in no u-RAF). Let $X_I \subseteq X$ be the molecules that inhibit at least one reaction. For $K \subseteq X_I$ let $\mathcal R - K$ be the set of reactions that have no product in $K$ and whose inhibitors (if any) all lie in $K$, and let $Q_K = (X, \mathcal R - K, C, F)$.

**Proposition.** $Q$ has a u-RAF if and only if $Q_K$ has an RAF for some $K \subseteq X_I$. Moreover, every maximal u-RAF of $Q$ is the maxRAF of $Q_K$ for some $K$, so the number of maximal u-RAFs of $Q$ is at most $|\{K \subseteq X_I : Q_K \text{ has an RAF}\}| \le 2^{|X_I|}$.

Consequently, although deciding whether a CRS with inhibition has a u-RAF is NP-hard in general, it can be done with $2^{|X_I|}$ runs of a polynomial-time maxRAF algorithm, which is tractable when the number of inhibitors is small.

## Depends on

- [Pseudo-RAF sets and the alternating maxRAF algorithm](pseudo-raf-sets-and-the-alternating-maxraf-algorithm.md)

## Expansion

Write $\mathcal R - K = R_1(K) \cap R_2(K)$ with $R_1(K) = \{r : \pi(r) \cap K = \emptyset\}$ and $R_2(K) = \{r : (x, r) \in I \Rightarrow x \in K\}$. (a) If $\mathcal R' \subseteq \mathcal R - K$, no reaction of $\mathcal R'$ is inhibited by a non-food molecule of $\mathrm{cl}_{\mathcal R'}(F)$: such a molecule is a product of some $r' \in \mathcal R' \subseteq R_1(K)$, hence not in $K$, while every inhibitor of a reaction in $R_2(K)$ lies in $K$. So every RAF of $Q_K$ is a u-RAF. (b) Conversely, a u-RAF $\mathcal R'$ is an RAF of $Q_K$ for $K = X_I \setminus \pi(\mathcal R')$: its reactions produce nothing in $K$, and any inhibitor of one of its reactions is not produced by $\mathcal R'$, hence lies in $K$. For a maximal u-RAF $\mathcal R'$ with this $K$, the maxRAF of $Q_K$ contains $\mathcal R'$ and is a u-RAF by (a), so it equals $\mathcal R'$.

## Sources

- W. Hordijk, J. I. Smith, M. Steel, "Algorithms for detecting and analysing autocatalytic sets", Algorithms for Molecular Biology (2015), section on RAFs with inhibition (definition of u-RAFs, Proposition 1 and its proof), <https://doi.org/10.1186/s13015-015-0042-8>, PMCID PMC4428007.
