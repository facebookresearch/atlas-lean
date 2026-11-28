# Consistency of maximum-likelihood tree estimation with gaps as missing data

Keep the setting of [Consistency of maximum-likelihood tree estimation on ungapped alignments](consistency-of-maximum-likelihood-tree-estimation.md): taxa $N = \{1, \dots, n\}$, trees with positive edge lengths, the metric $D$, Jukes–Cantor substitutions. Now an alignment $A_m$ is an $n \times m$ matrix over $\{A, C, G, T, -\}$, where $-$ marks a taxon with no letter homologous to that column. Sequences evolve from an unobserved root sequence by a continuous-time Markov process in which substitutions and indels are **independent**, and inserted letters are drawn from the substitution model's equilibrium distribution. For $S \subseteq N$, the **site category** $C(S)$ is the set of columns whose non-gap letters occur exactly in the taxa of $S$, so $A_m[S, C(S)]$ is ungapped. For a tree $T$, $T|_S$ is the subtree spanning $S$ with degree-two vertices suppressed and lengths adjusted so that $d_{T|_S}(a,b) = d_T(a,b)$ on $S$.

Treating gaps as missing data means scoring column $j$ by $\Pr[A_m[S, j] \mid T|_S]$, with $S$ its set of non-gap taxa, so

$$L(A_m \mid T) = \frac{1}{m}\sum_{S \subseteq N} \log \Pr\big[A_m[S, C(S)] \,\big|\, T|_S\big].$$

Assumptions on the indel process, both holding almost surely:

1. for every pair $a, b$, the number $K_{ab}$ of columns where neither $a$ nor $b$ has a gap tends to infinity;
2. for every $S \subseteq N$, either $|C(S)| = 0$ for all $m$ or $|C(S)| \to \infty$.

They hold for indel models with finite, position-uniform rates, such as the Thorne–Kishino–Felsenstein model, the long-indel model and the Poisson indel process.

**Theorem (consistency with gaps).** Under Assumptions 1 and 2, $D(\mathrm{ML}(A_m), T^*) \to 0$ with probability $1$ as $m \to \infty$.

Thus the only way standard maximum likelihood can fail on a correct alignment with gaps is when the substitution process degenerates, for example when there are no substitutions at all, so that only the gap pattern carries signal. The independence of indels and substitutions matters: when missing data correlate with the substitution process, distance and likelihood methods can be biased or inconsistent.

## Depends on

- [Consistency of maximum-likelihood tree estimation on ungapped alignments](consistency-of-maximum-likelihood-tree-estimation.md)

## Expansion

Apply the uniform separation lemma to each ungapped block $A_m[S, C(S)]$ with tree $T^*|_S$; this is valid for every $S$ with $|C(S)| \to \infty$. If $D(T, T^*) > \epsilon$, some pair $a, b$ has $|d_T(a,b) - d_{T^*}(a,b)| > \epsilon$. The columns where $a$ and $b$ are both present are infinitely many by Assumption 1 and lie in finitely many categories $C(S)$ with $S \supseteq \{a, b\}$, so some such category is infinite, and by Assumption 2 it grows without bound; for that $S$, $D(T|_S, T^*|_S) > \epsilon$. Hence the event "some $T$ with $D(T, T^*) > \epsilon$ scores at least as well as $T^*$" is contained in the union over the $2^n$ subsets $S$ of the corresponding ungapped events, and the union bound sends its probability to $0$. So $\Pr[D(\mathrm{ML}(A_m), T^*) \le \epsilon] \to 1$ for every $\epsilon > 0$.

## Sources

- J. Truszkowski and N. Goldman, "Maximum likelihood phylogenetic inference is consistent on multiple sequence alignments, with or without gaps", Systematic Biology 65(2) (2016), 328–333, Preliminaries (site categories, gaps as missing data), The Indel Process (Assumptions 1–2), Consistency for Gapped Alignments (Theorem 2, Eq. (1)), <https://doi.org/10.1093/sysbio/syv089> (PMC4748752).
