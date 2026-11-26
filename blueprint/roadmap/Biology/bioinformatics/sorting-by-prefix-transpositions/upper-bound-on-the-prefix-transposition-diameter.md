# Upper bound on the prefix transposition diameter

**Setting.** Model a genome with $n$ distinct markers as a permutation $\pi\in S_n$ of $\{0,1,\dots,n-1\}$. A *transposition* moves a contiguous sublist to another position; a *prefix transposition* is a transposition whose moved sublist starts at the first position, $(\pi_1,\dots,\pi_i)$ being reinserted after position $j>i$. The prefix transposition distance $d(\pi)$ is the least number of prefix transpositions sorting $\pi$ to the identity $I_n$, and the prefix transposition diameter is $D(n)=\max_{\pi\in S_n}d(\pi)$. An *adjacency* is a pair of consecutive symbols $x,x+1$ placed consecutively, and a permutation is *reduced* when no adjacencies remain (maximal sorted runs are contracted to single symbols). A *block* of $\pi$ is a sublist of at least two elements which, when sorted, is a substring of $I_n$.

**Theorem.** For every $n$,

$$D(n)\le n-\log_2 n.$$

This improves the successive upper bounds $n-1$ (Dias and Meidanis), $n-\log_8 n$ (Chitturi and Sudborough's sequence length algorithm), $n-\log_{9/2}n$ and $n-\log_{7/2}n$ (Chitturi), and the intermediate bounds $n-\log_{10/3}n$ and $n-\log_3 n$ obtained along the way. The known lower bound is $3n/4$ (Labarre); the reverse permutation $(n-1,\dots,1,0)$ can be sorted in $n-\lfloor n/4\rfloor$ prefix transpositions, and Dias, Meidanis and Fortuna conjectured that $n-\lfloor n/4\rfloor$ is the diameter.

## Expansion

Every prefix transposition changes at most three adjacencies, and a greedy move creating one new adjacency (a *single*) always exists for a reduced permutation, which gives the trivial bound $n-1$. The sequence length algorithm performs singles on a reduced permutation until it can perform a move creating two adjacencies (a *double*), then reduces and repeats. If a run of greedy moves moves $n$ symbols of which a fraction $1-\alpha$ is *skipped* before a double appears, the number of doubles over the whole run grows like $\log_{1/(1-\alpha)}n$, which gives the bound $n-\log_{1/(1-\alpha)}n$. The improvement to $\log_2 n$ amounts to showing that, in every case, at least half of the moved symbols are skipped. When this fails along the greedy sequence, the structure of a block (a sublist whose last visited symbol is its minimum and which contains a whole interval of values) is used to exhibit alternate moves that restore the half-skipped ratio.

## Sources

- Pramod P. Nair, "Upper Bounds to Genome Rearrangement Problem using Prefix Transpositions", arXiv:2205.04785 (2022), doctoral thesis: Chapter 2 (prefix transpositions, sorting reverse permutations, the sequence length algorithm), Chapters 3–4 (the $n-\log_{10/3}n$ and $n-\log_3n$ upper bound theorems), Chapter 5 (block definition and lemma, observations and the $n-\log_2 n$ upper bound theorem). <https://doi.org/10.48550/arXiv.2205.04785>
