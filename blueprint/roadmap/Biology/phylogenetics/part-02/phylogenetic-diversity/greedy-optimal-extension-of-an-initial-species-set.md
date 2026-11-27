# Greedy optimal extension of an initial species set

**Setting.** Let $T_S$ be a tree whose leaves are a species set $S$, with non-negative branch lengths. For $X \subseteq S$, $T_X$ is the smallest subtree of $T_S$ connecting $X$, and the *divergence* (phylogenetic diversity) $\delta(X)$ is the total branch length of $T_X$. For $x \in X$, the *terminal path* of $T_X$ leading to $x$ is the path from $T_{X\setminus\{x\}}$ to $x$. A set $Y$ is a *$k$-extension* of $X$ if it is obtained by adding $k$ species not in $X$. Given an initial set $I \subseteq S$ (for example, species already sequenced), $X$ is a *maximally divergent $k$-extension* ($k$-MDE) of $I$ if $X$ is a $k$-extension of $I$ and $\delta(Y) \le \delta(X)$ for every $k$-extension $Y$ of $I$. A 1-MDE of $X$ is a *greedy extension*, written $X^+$.

**Lemma.** If $2 \le |X| < |Y|$, there is a leaf $x \in Y \setminus X$ such that the path from $T_X$ to $x$ contains the whole terminal path of $T_Y$ leading to $x$.

**Theorem.** If $X$ is a $k$-MDE of $I$ and $2 \le |X| < |S|$, then every greedy extension $X^+$ is a $(k+1)$-MDE of $I$.

**Corollary (greedy is optimal from any start).** Starting from any initial set $I$, repeatedly adding the species that most increases $\delta$ produces, after $k$ steps, a $k$-MDE of $I$, for every $k$ with $|I| + k \ge 2$. In particular, starting from a maximally divergent set of $h \ge 2$ species, $k$ greedy steps give a maximally divergent set of $h + k$ species.

The condition $|X| \ge 2$ is needed: with $I = \emptyset$ and $k = 1$ every single species has divergence $0$, but not every single species starts an optimal pair.

## Depends on

- [Greedy maximization of phylogenetic diversity](greedy-maximization-of-phylogenetic-diversity.md)

## Expansion

Let $Y$ be any $(k+1)$-extension of $I$. By the lemma, $Y$ has a leaf $x \notin X$ whose terminal path in $T_Y$ lies inside the path from $T_X$ to $x$. Removing $x$ from $Y$ leaves a $k$-extension of $I$, so $\delta(Y) - (\text{terminal path of } x) \le \delta(X)$; adding $x$ to $X$ instead gains at least that terminal path, and the greedy step gains at least as much as adding $x$. Hence $\delta(X^+) \ge \delta(Y)$. The first greedy step from $I$ is a 1-MDE by definition, and induction on the number of steps gives the corollary. Practically, uncoordinated sequencing projects that each add the most divergent next genome, given what has already been sequenced, achieve the best long-run set of any size.

## Sources

- F. Pardi, N. Goldman, "Species choice for comparative genomics: being greedy works", PLoS Genetics 1 (2005) e71, Materials and Methods (definitions, Theorem 1, Lemma, Corollaries 1–2), <https://doi.org/10.1371/journal.pgen.0010071>, PMCID PMC1298936.
