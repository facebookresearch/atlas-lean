# Minimal DBN DAG equals the $q$-th order conditional dependence DAG

**Setting.** Expression levels $X_t=(X^1_t,\dots,X^p_t)$ of $p$ genes are observed at times $t=1,\dots,n$. A dynamic Bayesian network (DBN) represents the law of $X$ by a DAG whose edges point from time $t-1$ to time $t$. Assume
- (A1) $X$ is first-order Markov: $X_t\perp X_{1:t-2}\mid X_{t-1}$ for $t\ge3$;
- (A2) genes at a given time are conditionally independent given the past: $X^i_t\perp X^j_t\mid X_{1:t-1}$ for $i\ne j$.

For $j\in[p]$ let $X^{-j}_{t-1}$ denote the other $p-1$ genes at time $t-1$. Define the full-order DAG and, for $q<p$, the **$q$-th order conditional dependence DAG**

$$\mathcal{G}_{\min}:\ X^j_{t-1}\to X^i_t\iff X^i_t\not\perp X^j_{t-1}\mid X^{-j}_{t-1};\qquad \mathcal{G}^{(q)}:\ X^j_{t-1}\to X^i_t\iff X^i_t\not\perp X^j_{t-1}\mid X^{Q}_{t-1}\ \ \forall\,Q\subseteq[p]\setminus\{j\},\ |Q|=q .$$

**Results.**
1. *(Minimal DBN.)* Under (A1)–(A2) the law of $X$ admits a DBN representation according to $\mathcal{G}_{\min}$, and $\mathcal{G}_{\min}$ is the smallest subgraph of the complete time-lagged DAG with this property.
2. *(Low order suffices for sparse networks.)* If every gene has at most $q$ parents in $\mathcal{G}_{\min}$, then a non-edge of $\mathcal{G}_{\min}$ is a non-edge of $\mathcal{G}^{(q)}$; hence $\mathcal{G}^{(q)}\subseteq\mathcal{G}_{\min}$ for all $q$ at least the maximal parent number.
3. *(Faithfulness.)* If the law is faithful to $\mathcal{G}_{\min}$ (unfaithful Gaussian or discrete parameters have Lebesgue measure zero), then $\mathcal{G}_{\min}\subseteq\mathcal{G}^{(q)}$ for every $q<p$, so $\mathcal{G}_{\min}=\mathcal{G}^{(q)}$ as soon as $q$ is at least the maximal number of parents.
4. *(Gaussian, $q=1$.)* For a Gaussian process with at most one parent per gene in $\mathcal{G}_{\min}$, $\mathcal{G}_{\min}=\mathcal{G}^{(1)}$, without assuming faithfulness.

## Expansion

(A1)–(A2) make each $X^i_t$ depend only on the previous time slice, so the DBN factorization reduces to choosing, for each $i$, a parent set in $X_{t-1}$, and the minimal such set is given by full-order conditional dependence. Conditioning on all $p-1$ other genes is infeasible when $p\gg n$, as in gene expression time series. If a gene has at most $q$ parents, a non-parent is separated from it, in the moral graph of the relevant ancestral set, by some set of $q$ variables, so it is also removed by some order-$q$ test; faithfulness gives the reverse inclusion. This justifies the two-step G1DBN procedure: first estimate $\mathcal{G}^{(1)}$ by testing all first-order partial regressions, then prune it to approximate $\mathcal{G}_{\min}$.

## Sources

- Sophie Lèbre, "Inferring dynamic genetic networks with low order independencies", arXiv:0704.2551 (2007), Assumptions 1–2, Proposition 3, Definition 4, Propositions 4–6 and Corollaries 1–2 (Sections 1–2), <https://doi.org/10.48550/arXiv.0704.2551>.
