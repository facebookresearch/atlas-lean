# Expected AUC of a ranking under posterior membership probabilities

Let $G$ be a graph with $n$ vertices, let $\mathcal M$ be a random vertex set (the active module) with $|\mathcal M| = m$, $0 < m < n$, and let $W = w$ be observed vertex weights. For a ranking $v_1, v_2, \dots, v_n$ of the vertices (rank $1$ first), put $p_i = P(v_i \in \mathcal M \mid W = w)$. The area under the ROC curve of the ranking as a classifier of $\mathcal M$ has expectation

$$E[\mathrm{AUC}] = 1 - \frac{1}{m(n - m)}\Bigl(\sum_{i=1}^n i\,p_i - \frac{m(m+1)}{2}\Bigr).$$

Hence, among all rankings, the expected AUC is maximized by ordering vertices by decreasing $p_i$. If $m = |\mathcal M|$ is random (supported on $\{1, \dots, n-1\}$), conditioning on $|\mathcal M| = m$ gives $E[\mathrm{AUC}] = 1 - \sum_{i=1}^n i\,q_i + E\big[\tfrac{|\mathcal M|+1}{2(n - |\mathcal M|)} \mid W = w\big]$, where $q_i = \sum_{m=1}^{n-1} P(|\mathcal M|=m \mid W=w)\,P(v_i \in \mathcal M \mid |\mathcal M|=m, W=w)/\big(m(n-m)\big)$, so expected AUC is maximized by ordering vertices by decreasing $q_i$. For random $|\mathcal M|$ the source prints $1-\frac{1}{\mathbb E|\mathcal M|\cdot|G\setminus\mathcal M|}\big(\sum_i i\,p'_i-\frac{\mathbb E|\mathcal M|(|\mathcal M|+1)}{2}\big)$ (after Lemma 1), a ratio of expectations, which is not the expected AUC in general; the form here follows from Lemma 1 by conditioning on $|\mathcal M|=m$ and averaging over $m$.

## Expansion

The AUC is the fraction of (module, non-module) pairs in which the module vertex is ranked higher; if $R$ is the sum of the ranks of the $m$ module vertices, the number of misordered pairs is $R - m(m+1)/2$, so $\mathrm{AUC} = 1 - (R - m(m+1)/2)/(m(n-m))$. Linearity of expectation gives $E[R] = \sum_i i\,p_i$, and by the rearrangement inequality this sum is smallest when larger $p_i$ receive smaller ranks. The probabilities $p_i$ are estimated by Markov chain Monte Carlo over connected subgraphs.

## Sources

- N. Alexeev, J. Isomurodov, V. Sukhov, G. Korotkevich and A. Sergushichev, "Markov chain Monte Carlo for active module identification problem", BMC Bioinformatics 21 (Suppl. 6) (2020) 261, <https://doi.org/10.1186/s12859-020-03572-9>, PMCID PMC7672893. Lemma 1 (proof in Appendix S1).
