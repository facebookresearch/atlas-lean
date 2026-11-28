# Generative mutual exclusivity model and test

**Data.** A binary matrix with $N$ rows (patients) and $n$ columns (genes of a candidate pattern), entry $1$ recording an observed alteration.

**Mutual exclusivity model.** Independently for each patient:

1. a hidden coverage indicator $Z \sim \mathrm{Bernoulli}(\gamma)$, with coverage $\gamma \in [0,1]$;
2. if $Z = 1$, one gene $X$ is chosen uniformly among the $n$ genes and is truly altered (the exclusive alteration);
3. in a covered patient each of the other $n-1$ genes is independently truly altered with impurity probability $\delta \in [0,1)$; an uncovered patient has no true alterations in the pattern;
4. the observed status of each gene equals its true status except for false positives (a true $0$ recorded as $1$ with probability $\alpha$) and false negatives (a true $1$ recorded as $0$ with probability $\beta$), independently across genes.

The likelihood of an observed row depends only on the number $k$ of observed alterations in it, so with $c_k$ the number of rows containing exactly $k$ ones the data log-likelihood is $\sum_{k=0}^{n} c_k \log p_k(\gamma, \delta, \alpha, \beta)$.

**Error-free case** ($\alpha = \beta = 0$). Then

$$p_0 = 1 - \gamma, \qquad p_k = \gamma\, \frac{k}{n}\, \delta^{k-1} (1-\delta)^{n-k} \quad (1 \le k \le n),$$

and the maximum likelihood estimates are

$$\hat\gamma = \frac{1}{N}\sum_{k \ge 1} c_k, \qquad \hat\delta = \frac{\sum_{k \ge 1} (k-1)\, c_k}{(n-1)\sum_{k \ge 1} c_k}.$$

With errors, the parameters are identifiable for patterns of $n \ge 3$ genes (Proposition 1) and are estimated by an EM algorithm initialized at the error-free estimates.

**Independence model.** Gene $j$ is altered independently with probability $q_j$, estimated by its alteration frequency $\hat q_j = N_j/N$.

**Test.** The two models are not nested. With pointwise log-likelihood ratios $\ell_i = \log p^{\mathrm{ME}}(y_i) - \log p^{\mathrm{IND}}(y_i)$ at the maximum likelihood estimates, sample standard deviation $\hat\omega$, and a correction for the difference in numbers of free parameters, Vuong's statistic

$$T = \frac{\sum_i \ell_i - \text{(parameter-count correction)}}{\sqrt{N}\, \hat\omega}$$

is asymptotically standard normal when both models are equally close in Kullback–Leibler divergence to the truth; a large $T$ (small one-sided $p$-value) supports mutual exclusivity.

## Expansion

In a covered row the exclusive gene can be any of the $k$ observed ones, each chosen with probability $1/n$, and the remaining $k-1$ alterations are impurities among $n-1$ candidates, giving $p_k$; uncovered rows are empty, so a nonempty row certifies coverage. Splitting the log-likelihood into $\big(\sum_{k\ge1}c_k\big)\log\gamma + c_0\log(1-\gamma)$ and a binomial term $\sum_{k\ge1}c_k[(k-1)\log\delta + (n-k)\log(1-\delta)]$ gives the closed-form estimates. Ignoring false positives inflates impurity and can reverse the ranking of patterns, which is why the full model carries error rates. Because the likelihood depends only on the row counts $c_k$, each EM iteration costs $O(n)$ after one pass over the data. Vuong's test compares non-nested models by the mean of pointwise log-likelihood ratios, standardized by their spread, rather than by a chi-square approximation.

## Sources

- E. Szczurek, N. Beerenwinkel, "Modeling mutual exclusivity of cancer mutations", PLoS Computational Biology 10 (2014) e1003503, Results ("Modeling and testing for mutual exclusivity", Proposition 1) and Materials and Methods (mutual exclusivity model, parameter estimation without and with errors, Box 1, independence model, testing via Vuong's statistic), <https://doi.org/10.1371/journal.pcbi.1003503>.
- Q. H. Vuong, "Likelihood ratio tests for model selection and non-nested hypotheses", Econometrica 57 (1989) 307–333, <https://doi.org/10.2307/1912557>.
