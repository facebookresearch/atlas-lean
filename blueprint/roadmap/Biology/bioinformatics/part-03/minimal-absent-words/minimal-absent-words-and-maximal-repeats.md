# Minimal absent words and maximal repeats

**Setting.** Let $S$ be a string over a finite alphabet $\Sigma$, with virtual end characters $S[0] = \#$ and $S[|S| + 1] = \dagger$ not in $\Sigma$. For a substring $\alpha$ of $S$ with occurrence set $P_\alpha$, let $\mathcal{L}_\alpha$ and $\mathcal{R}_\alpha$ be the sets of characters immediately left and right of the occurrences of $\alpha$, and let

$$\mathcal{E}_\alpha = \{ (S[p-1], S[p + |\alpha|]) : p \in P_\alpha \} \subseteq (\Sigma \cup \{\#\}) \times (\Sigma \cup \{\dagger\})$$

be the set of enclosing character pairs.

A **maximal repeated pair** is a triple $(p_1, p_2, \alpha)$ with $p_1 \ne p_2$ occurrences of $\alpha$ such that $S[p_1 - 1] \ne S[p_2 - 1]$ and $S[p_1 + |\alpha|] \ne S[p_2 + |\alpha|]$; $\alpha$ is a **maximal repeat** if some maximal repeated pair has the form $(p_1, p_2, \alpha)$.

**Definition (minimal absent word).** A string $\gamma$ with $|\gamma| \ge 3$ is a minimal absent word of $S$ if $\gamma$ is not a substring of $S$ but both $\gamma[2..|\gamma|]$ and $\gamma[1..|\gamma| - 1]$ are.

**Theorem 1.** If $l \alpha r$ (with $l, r \in \Sigma$) is a minimal absent word of $S$, then $\alpha$ is a maximal repeat of $S$.

**Theorem 2.** For $l \in \mathcal{L}_\alpha \cap \Sigma$ and $r \in \mathcal{R}_\alpha \cap \Sigma$, the string $l \alpha r$ is a minimal absent word of $S$ if and only if $(l, r) \notin \mathcal{E}_\alpha$.

**Consequences.** Since a string of length $|S|$ has at most $|S|$ maximal repeats, and each contributes at most $|\Sigma|^2$ pairs $(l, r)$, $S$ has at most $|S| \, |\Sigma|^2$ minimal absent words of length at least $3$. Maximal repeats are the path labels of the left-diverse internal nodes of the suffix tree of $S$, so all minimal absent words can be enumerated from a suffix tree, or equivalently from a suffix array with its LCP and Burrows-Wheeler arrays, in time linear in $|S|$ plus the output size.

## Depends on

- [Suffix array](../../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [Burrows–Wheeler transform](../../../../ComputerScience/string-algorithms/burrows-wheeler-transform-and-fm-index/bwt.md)

## Proof depends on

- [Suffix tree](../../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-tree/suffix-tree.md)

## Expansion

If $l \alpha r$ is absent while $l \alpha$ and $\alpha r$ occur, at positions $p_1$ and $p_2$ say, the character after the occurrence of $l \alpha$ cannot be $r$ and the character before the occurrence of $\alpha r$ cannot be $l$; hence the two occurrences of $\alpha$ differ on both sides, a maximal repeated pair. Theorem 2 restates minimal absence locally: $l \alpha$ and $\alpha r$ occur exactly when $l \in \mathcal{L}_\alpha$ and $r \in \mathcal{R}_\alpha$, and $l \alpha r$ occurs exactly when $(l, r)$ encloses some occurrence of $\alpha$. Minimal absent words (unlike all absent words or nullomers) form a set of linear size that determines the string, which makes them a compact signature for comparing genomes.

## Sources

- A. J. Pinho, P. J. S. G. Ferreira, S. P. Garcia, J. M. O. S. Rodrigues, "On finding minimal absent words", BMC Bioinformatics 10 (2009) 137, Definitions 1-5, Theorems 1-2, <https://doi.org/10.1186/1471-2105-10-137> (PMC2698904).
