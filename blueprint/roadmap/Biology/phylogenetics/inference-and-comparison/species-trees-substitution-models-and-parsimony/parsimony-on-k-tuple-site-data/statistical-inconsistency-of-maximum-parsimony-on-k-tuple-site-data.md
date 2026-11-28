# Statistical inconsistency of maximum parsimony on k-tuple-site data

**Setting.** An alignment on a taxon set $X$ over an alphabet $\mathcal A$ with $r$ states can be read as *$k$-tuple-site data*: each block of $k$ consecutive sites becomes one character $X\to\mathcal A^k$ with $r^k$ states, and its parsimony score on a tree $T$ is the minimum number of edges whose endpoints carry different $k$-tuples. Maximum parsimony (MP) on $k$-tuple data returns the tree minimizing the total score. Characters evolve i.i.d. under the symmetric **$N_r$ model**: along edge $e$ each state changes to each other given state with probability $\mathsf p_e$ (so $\mathsf p_e\in[0,1/r]$). MP is *statistically consistent* for a generating tree $(T,\theta_T)$ if, as the number of characters grows, it returns $T$ with probability tending to one; equivalently, $T$ uniquely minimizes the expected score $\mu_k(T'\mid(T,\theta_T))$.

**Theorem (four taxa; Steel and Penny).** For four sequences and any i.i.d. model, MP is consistent on $k$-tuple-site data if and only if it is consistent on single-site data. Since single-site MP is inconsistent in the Felsenstein zone, $k$-tuple MP is inconsistent for four taxa as well.

**Theorem (five taxa).** For five sequences MP is statistically inconsistent
1. on $2$-tuple-site data under the i.i.d. $N_2$ model,
2. on $2$-tuple-site data under the i.i.d. $N_4$ model,
3. on $3$-tuple-site data under the i.i.d. $N_2$ model,
4. on $3$-tuple-site data under the i.i.d. $N_4$ model.

An explicit witness for case 1: on a five-taxon tree $T_1$ with two long edges (substitution probability $p$) and five short edges ($q$), taking $p=91/256\approx0.35547$ and $q=0.1$ makes two other trees have strictly smaller expected $2$-tuple parsimony score than $T_1$ (whose expected score is $1.000957$).

**Observation (no equivalence for five taxa).** For five sequences and $r\in\{2,4\}$, the four-taxon equivalence fails: there are parameter values $(p,q)$ where MP is consistent on single-site data but inconsistent on $2$-tuple data and vice versa (the inconsistency boundaries cross, e.g. at $q\approx0.150756$ for $r=2$), and likewise between $2$-tuple and $3$-tuple data (crossings at $q\approx0.172413$ for $r=2$ and $q\approx0.150079$ for $r=4$).

## Expansion

Expected parsimony scores of $k$-tuple characters are computed exactly by enumerating the $r^{5k}$ leaf patterns (reduced by symmetry) with their $N_r$ probabilities on $T_1$ and Fitch-type scores on each of the $15$ unrooted five-taxon trees. Long-branch attraction persists because a $k$-tuple changes on an edge whenever any of its sites changes, so two long edges still accumulate parallel tuple changes more often than the short internal edges record true shared changes. Blockwise analysis (for example, of codons) therefore does not remove MP's inconsistency, and with more than four taxa it changes the inconsistency zone in either direction rather than reproducing the single-site one.

## Sources

- Michelle Galla, Kristina Wicke, Mareike Fischer, "Statistical Inconsistency of Maximum Parsimony for k-Tuple-Site Data", Bulletin of Mathematical Biology 81 (2019), 1173–1200, <https://doi.org/10.1007/s11538-018-00552-2>. Published version of arXiv:1706.05568, cited next; locators there refer to the arXiv version.
- Michelle Galla, Kristina Wicke, Mareike Fischer, "On the statistical inconsistency of Maximum Parsimony for $k$-tuple-site data", arXiv:1706.05568 (2017): Section 1.1 (definitions, $N_r$ model), Theorem 1 (Steel–Penny), Theorem 2 and its proof, the first Observation, Theorem 3, the second Observation (Section 2). <https://doi.org/10.48550/arXiv.1706.05568>
