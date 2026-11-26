# Maximal perfect haplotype blocks and linear-time enumeration

**Definition.** Let $S = (s_1,\dots,s_k)$ be $k$ sequences of common length $n$ over a constant-size alphabet $\Sigma$ (the rows of a haplotype matrix; columns are variable sites). Write $s[i,j]$ for the substring from position $i$ to $j$ and $S|_K$ for the rows indexed by $K$. A *maximal perfect haplotype block* is a triple $(K,i,j)$ with $K \subseteq \{1,\dots,k\}$, $|K| \ge 2$ and $1 \le i \le j \le n$ such that

1. (equality) $s[i,j] = t[i,j]$ for all $s,t \in S|_K$;
2. (left-maximality) $i = 1$ or $s[i-1] \ne t[i-1]$ for some $s,t \in S|_K$;
3. (right-maximality) $j = n$ or $s[j+1] \ne t[j+1]$ for some $s,t \in S|_K$;
4. (row-maximality) there is no $K' \supsetneq K$ with $s[i,j] = t[i,j]$ for all $s,t \in S|_{K'}$.

**Positional BWT arrays.** For each column $l$, let $a_l$ be the permutation of $\{1,\dots,k\}$ that sorts the prefixes $s[1,l]$ colexicographically (right to left), $a_l^{-1}$ its inverse, and $d_l$ the divergence array: $d_l[1] = l+1$ and, for $1 < r \le k$, $d_l[r] = 1 + \max\{j \le l : s_{a_l[r]}[j] \ne s_{a_l[r-1]}[j]\}$ (with $\max\emptyset = 0$).

**Definition 2 (available block).** A quadruple $(i,j;x,y)$ with $1 \le i \le j \le n$ and $1 \le x < y \le k$ is an *available block* if $d_j[r] \le i$ for all $r \in [x+1,y]$; $d_j[r] = i$ for at least one $r \in [x+1,y]$; and ($x = 1$ or $d_j[x] > i$) and ($y = k$ or $d_j[y+1] > i$). These encode equality, left-maximality and row-maximality. Then

- (Lemma 1) for every maximal perfect haplotype block $(K,i,j)$, the set $\{a_{j}^{-1}[r] : r \in K\}$ of ranks is a contiguous range $[x,y]$ and $(i,j;x,y)$ is an available block;
- at most $k$ available blocks end at any column $l$, since they correspond to distinct branching nodes of the trie of the reversed prefixes $s_1[1,l],\dots,s_k[1,l]$, which has at most $k$ leaves;
- (Lemma 2) an available block $(i,j;x,y)$ is a maximal perfect haplotype block if and only if $j = n$ or $|\{S[a[r]][j+1] : r \in [x,y]\}| > 1$.

**Theorem (linear time).** All maximal perfect haplotype blocks of $S$ can be found in $O(kn)$ time, linear in the size of the input matrix. Consequently there are $O(kn)$ such blocks in total.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

The positional BWT is built column by column in $O(k)$ time per column. At column $l$ the available blocks are the LCP intervals of the trie whose LCP array is $\mathrm{LCP}_l[r] = l - d_l[r] + 1$, where $d_l$ is the divergence array; they are enumerated in $O(k)$ time by the standard stack-based LCP-interval algorithm. Right-maximality is tested in constant time per block by a bit vector $V_j$ with $V_j[r] = 1$ iff the next symbols of rows $a_j[r-1]$ and $a_j[r]$ differ, together with its prefix sums: the block is right-maximal iff $V_j[x+1..y]$ contains a 1. Summing $O(k)$ work over $n$ columns gives $O(kn)$. An alternative algorithm with the same bound uses a generalized suffix tree.

## Sources

- J. Alanko, H. Bannai, B. Cazaux, P. Peterlongo, J. Stoye, "Finding all maximal perfect haplotype blocks in linear time", Algorithms for Molecular Biology 15 (2020) 2, Definitions 1–2, Lemmas 1–2, <https://doi.org/10.1186/s13015-020-0163-6>, PMCID PMC7008532.
