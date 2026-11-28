# Extending contact matrices by a binary attribute with homophily

**Setting.** A population is stratified over a combined attribute space $A$ (for example age groups), with group sizes $N_i$, and $C_{ij}\ge0$ is the mean number of contacts an individual of group $i$ has with group $j$. $C$ is **reciprocal** if $N_iC_{ij}=N_jC_{ji}$ for all $i,j$, so contacts counted from both sides agree. Now add a binary attribute (for example vaccinated or not) with population prevalence $P$, giving the extended space $A^\star=A\times\{0,1\}$ with known group sizes $N^\star$. For an undirected contact structure with attribute prevalence $p\in(0,1)$, let $\phi$ be the proportion of contacts between individuals with the same attribute value and $\mathbb E(\phi)=p^2+(1-p)^2$ its value under random mixing; the **homophily** is $h=(\phi-\mathbb E\phi)/(1-\mathbb E\phi)\in[0,1]$ if $\phi\ge\mathbb E\phi$ and $h=(\phi-\mathbb E\phi)/\mathbb E\phi\in[-1,0)$ otherwise, so $h=1$ is complete segregation, $h=0$ random mixing and $h=-1$ complete disassortativity.

**Theorem 2.1 and Corollary 2.2 (reciprocity).** For any contact matrix $C$, the matrix $\tilde C_{ij}=(N_iC_{ij}+N_jC_{ji})/(2N_i)$ is reciprocal; for a reciprocal $C$ the total number of contacts in the population is $\tfrac12\sum_{i,j}N_iC_{ij}$.

**Admissible extensions (Definition 4.1).** An extended matrix $C^\star$ on $A^\star$ is admissible if it is (a) reciprocal; (b) preserves each individual's total contacts, $\sum_jC^\star_{(i,0),j}=\sum_jC^\star_{(i,1),j}=\sum_jC_{ij}$; (c) reproduces the original pattern, $\sum_v\frac{N^\star_{(i,v)}}{N_i}\sum_wC^\star_{(i,v),(j,w)}=C_{ij}$; and (d) has the prescribed homophily, $\phi=\mathbb E(\phi)(1-h)+h$ for $h\ge0$ and $\phi=\mathbb E(\phi)(1+h)$ for $h<0$. These conditions are linear in the entries of $C^\star$.

**Theorem 4.2 (feasible homophily interval).** There are $h_{\min}\le0\le h_{\max}$ in $[-1,1]$ such that the linear system (a)-(d) has a non-negative solution $C^\star$ if and only if $h\in[h_{\min},h_{\max}]$.

## Expansion

Symmetrizing by averaging the two counts of each contact type enforces reciprocity while keeping total contacts. The admissibility conditions form a linear system in the unknown entries of $C^\star$; its non-negative solution set, intersected with a one-parameter family indexed by the homophily constraint, is a polytope that varies linearly with $h$, so the set of feasible $h$ is an interval. Random mixing ($h=0$), which splits each contact proportionally to the attribute prevalences, is always feasible. Extreme homophily can be infeasible when the attribute's prevalence differs strongly across the original groups, because preserving each group's contact totals then forces cross-attribute contacts. Projected matrices feed directly into next-generation matrices for vaccination or behaviour-stratified epidemic models.

## Sources

- C. Kadelka, "Projecting social contact matrices to populations stratified by binary attributes with known homophily", *Mathematical Biosciences and Engineering* 20(2) (2022), 3282–3300, Theorem 2.1, Corollary 2.2, Definitions of homophily (Section 3) and admissible extensions (Section 4), Theorem 4.2, <https://doi.org/10.3934/mbe.2023154> (preprint arXiv:2207.12328).
