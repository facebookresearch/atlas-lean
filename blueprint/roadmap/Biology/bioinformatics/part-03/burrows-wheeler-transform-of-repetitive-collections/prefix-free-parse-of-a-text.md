# Prefix-free parse of a text

Fix a window length $w \ge 1$, a set $E \subseteq \Sigma^w$ of trigger strings, and special symbols $\#$ and $\dashv$ lexicographically smaller than every letter of $\Sigma$; let $E' = E \cup \{\#, \dashv^{w}\}$. For a text $T[0..n-1]$ over $\Sigma$, the **dictionary** $D$ is the maximal set of strings $d$ such that

1. $d$ is a substring of $\# T \dashv^{w}$;
2. exactly one proper prefix of $d$ is in $E'$;
3. exactly one proper suffix of $d$ is in $E'$;
4. no other substring of $d$ is in $E'$.

The **parse** $P$ lists the occurrences of elements of $D$ in $\#T\dashv^{w}$ from left to right, each identified by its lexicographic rank in $D$; consecutive phrases overlap in exactly $w$ characters. $D$ and $P$ are computed in one scan of $T$ (in practice $E$ is chosen implicitly as the windows whose Karp–Rabin fingerprint is $0$ modulo a parameter). Let $S$ be the set of suffixes of length greater than $w$ of elements of $D$.

**Lemmas.**

1. $S$ is prefix-free.
2. If $s, s' \in S$ and $s \prec s'$, then $sx \prec s'x'$ for all strings $x, x'$.
3. Every suffix $x$ of $\#T\dashv^{w}$ with $|x| > w$ has exactly one prefix in $S$; call it $f(x)$.
4. For such suffixes $x, x'$, $f(x) \prec f(x') \Rightarrow x \prec x'$.
5. The permutation sorting $T[0..n-1]\dashv^{w}, \dots, T[n-1]\dashv^{w}, \#T\dashv^{w}$ also sorts the suffixes of $T' = T\dashv$.

## Depends on

- [Suffix array](../../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)

## Expansion

If $s \in S$ were a proper prefix of $s' \in S$, the last $w$ characters of $s$ (an element of $E'$) would occur strictly inside $s'$, so the dictionary phrase ending in $s'$ would contain three trigger occurrences, contradicting condition 4; this gives Lemma 1, and Lemma 2 follows because two non-prefix strings already differ within their common length. For Lemma 3, the phrase spanning from the last trigger at or before the start of $x$ to the first trigger strictly after it is an element of $D$, and its tail starting at $x$ is the unique element of $S$ prefixing $x$. Lemma 4 is Lemma 2 applied to $f(x)$ and $f(x')$. Together they say that comparing short dictionary suffixes already orders most text suffixes.

## Sources

- C. Boucher, T. Gagie, A. Kuhnle, B. Langmead, G. Manzini and T. Mun, "Prefix-free parsing for building big BWTs", Algorithms for Molecular Biology 14 (2019), 13, "Theory of prefix free parsing", Lemmas 1–5, <https://doi.org/10.1186/s13015-019-0148-5>, PMCID: PMC6534911.
