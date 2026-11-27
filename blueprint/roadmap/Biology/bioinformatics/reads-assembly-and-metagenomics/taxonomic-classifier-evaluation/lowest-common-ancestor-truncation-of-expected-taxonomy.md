# Lowest-common-ancestor truncation of expected taxonomy

Let $\mathcal{T}$ be a rooted taxonomy of fixed depth $R$ (ranks $1, \dots, R$, for example domain through species), so that every label is a path $t = (t_1, \dots, t_R)$ from the root. Let $D = \{(x_s, t^{(s)})\}_{s \in S}$ be a reference database of sequences with labels, and let $S = S_1 \sqcup \cdots \sqcup S_K$ be a partition into $K$ folds, stratified so that each taxonomic group is spread across folds. For fold $\kappa$ the training set is $D_{-\kappa} = \{(x_s,t^{(s)}) : s \notin S_\kappa\}$.

For a query $s \in S_\kappa$ define its *expected taxonomy*

$$e(s,\kappa) \;=\; \operatorname{lca}\bigl(t^{(s)}, \; \{\, t^{(s')} : s' \notin S_\kappa \,\}\bigr) \;=\; \bigl(t^{(s)}_1, \dots, t^{(s)}_{d}\bigr), \qquad d \;=\; \max_{s' \notin S_\kappa} \; \lvert t^{(s)} \wedge t^{(s')} \rvert,$$

where $\lvert t \wedge t' \rvert$ is the length of the longest common prefix of two label paths. Classifier performance is scored at each rank against $e(s,\kappa)$, not against $t^{(s)}$, by precision, recall and $F$-measure.

Two properties follow immediately.

1. **Truncation.** $e(s,\kappa)$ is a prefix of $t^{(s)}$, with $e(s,\kappa) = t^{(s)}$ exactly when some other sequence of the training fold carries the full label $t^{(s)}$. A query that is a taxonomic singleton with respect to $D_{-\kappa}$ therefore has its expected label truncated to the deepest rank at which its clade is represented in the training data.
2. **Upper bound.** Training and testing on the whole database, $D_{-\kappa} = D$ with the query itself included, gives $e(s) = t^{(s)}$ for every $s$ and an exact match in the reference set, so the resulting accuracy is an upper bound on what the database supports, attained in the unrealistic case where every query is already in the reference. Decreasing $K$ enlarges the held-out folds, increases the number of singletons, and so lowers the expected depth $d$, making the task harder.

## Remarks

Scoring against $t^{(s)}$ rather than $e(s,\kappa)$ punishes a classifier for the one answer it could not give: if no training sequence belongs to the species of the query, no classifier trained on $D_{-\kappa}$ can output that species, and the honest target is the deepest ancestor the training data can resolve. Truncation makes the evaluation measure what the classifier controls, assignment to a represented clade, rather than coverage of the database.

The same construction explains what database comparisons are measuring. Reported accuracies depend jointly on the classifier and on the redundancy of the labels: a database with many sequences per species has few singletons, keeps $d = R$ for most queries, and looks accurate at species rank; a database with sparse, highly resolved labels has many singletons and is penalized at the deepest ranks unless the truncation is applied. Companion summaries of a database, such as the Shannon entropy

$$H(X) = -\sum_{i=1}^{n} P(x_i)\,\log P(x_i)$$

of label frequencies at each rank or of sequence and $k$-mer frequencies, quantify that redundancy directly, combining richness and evenness in one number.

## Sources

- M. S. Robeson II, D. R. O'Rourke, B. D. Kaehler, M. Ziemski, M. R. Dillon, J. T. Foster, N. A. Bokulich, "RESCRIPt: Reproducible sequence taxonomy reference database management", PLoS Computational Biology 17(11) (2021) e1009581, Methods, "Reference database benchmarks" (definitions of `evaluate-cross-validate`, `evaluate-fit-classifier` and the entropy measure), <https://doi.org/10.1371/journal.pcbi.1009581> (PMC8601625).
