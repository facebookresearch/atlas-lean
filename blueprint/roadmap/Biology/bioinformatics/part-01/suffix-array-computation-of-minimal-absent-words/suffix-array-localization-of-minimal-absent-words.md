# Suffix-array localization of minimal absent words

**Definitions.** Let $y = y[0]\dots y[n-1]$ be a word over an ordered alphabet $\Sigma$ of constant size $\sigma$. A word $x$ of length $m \ge 2$ is a *minimal absent word* of $y$ if $x$ does not occur in $y$ but every proper factor of $x$ does. For a factor $x_1$ of $y$ define the left-context sets

$$B_1(x_1) = \{\, y[j-1] : x_1 \text{ occurs at position } j \,\}, \qquad B_2(x_1) = \{\, y[j-1] : x_1[0..|x_1|-2] \text{ occurs at position } j \,\}.$$

Let $\mathrm{SA}$ be the suffix array of $y$ and $\mathrm{LCP}[i]$ the length of the longest common prefix of the suffixes at ranks $i-1$ and $i$.

**Lemma (context characterization).** $x$ is a minimal absent word of $y$ if and only if $x[0] \in B_2(x_1) \setminus B_1(x_1)$, where $x_1 = x[1..m-1]$.

**Lemma (localization).** If $x$ is a minimal absent word of $y$ and $x_1 = x[1..m-1]$, then for some rank $i \in [0, n-1]$ either $x_1 = y[\mathrm{SA}[i] .. \mathrm{SA}[i] + \mathrm{LCP}[i]]$ or $x_1 = y[\mathrm{SA}[i] .. \mathrm{SA}[i] + \mathrm{LCP}[i+1]]$.

**Theorem.** Hence all minimal absent words of $y$ are obtained by computing $B_1$ and $B_2$ for the $2n$ candidate factors $S_{2i} = y[\mathrm{SA}[i]..\mathrm{SA}[i]+\mathrm{LCP}[i]]$ and $S_{2i+1} = y[\mathrm{SA}[i]..\mathrm{SA}[i]+\mathrm{LCP}[i+1]]$ and reporting each letter of $B_2(S_j) \setminus B_1(S_j)$; with a top-down and a bottom-up stack pass over $\mathrm{SA}$ and $\mathrm{LCP}$ this takes $O(n)$ time and space, each minimal absent word being reported in constant time as a tuple $\langle a, (i,j)\rangle$ meaning $x = a\, y[i..j]$.

For example, $y = \mathtt{AABABABB}$ has exactly seven minimal absent words: $\mathtt{AAA}$, $\mathtt{AABABB}$, $\mathtt{AABB}$, $\mathtt{BAA}$, $\mathtt{BABABA}$, $\mathtt{BBA}$, $\mathtt{BBB}$.

## Expansion

If $p \in B_2(x_1) \setminus B_1(x_1)$, then $p\,x_1[0..|x_1|-2]$ and $x_1$ both occur while $p\,x_1$ does not, so every proper factor of $p\,x_1$ occurs; the converse reads the same facts backwards. For localization, take an occurrence of $x[0..m-2]$ at $j$ and of $x_1$ at $k$: the suffixes starting at $j+1$ and $k$ share exactly $x_2 = x[1..m-2]$ as longest common prefix (it cannot extend, or $x$ would occur), so all $\mathrm{LCP}$ values between their ranks are at least $m-2$ with equality somewhere; the extreme rank achieving equality spells $x_1$ through one of the two candidate windows. Since there are only $2n$ candidates and each left-context set has at most $\sigma$ letters, the number of minimal absent words is $O(\sigma n)$, matching the known upper bound, and the algorithm is linear for fixed $\sigma$. Minimal absent words are used as alignment-free signatures for comparing genomes.

## Sources

- C. Barton, A. Heliou, L. Mouchard, S. P. Pissis, "Linear-time computation of minimal absent words using suffix array", BMC Bioinformatics 15:388 (2014), Lemmas 1-2 and Theorem 1, <https://doi.org/10.1186/s12859-014-0388-9>, PMCID PMC4297395.
