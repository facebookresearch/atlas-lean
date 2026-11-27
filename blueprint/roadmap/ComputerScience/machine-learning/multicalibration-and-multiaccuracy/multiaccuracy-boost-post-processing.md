# Black-box post-processing to multiaccuracy does no harm on audited subgroups

Let $D$ be a distribution over $X \times \{0,1\}$, let $\mathcal{C}$ be a class of functions $c : X \to [-1,1]$, and write $\ell_D(p) = \mathbb{E}[-y\log p(x) - (1-y)\log(1-p(x))]$ for the cross-entropy loss. Multiaccuracy Boost post-processes an initial predictor $p_0 : X \to (0,1)$, using only black-box access to it: it partitions $X$ into $X_0 = \{p_0 \le \tfrac12\}$ and $X_1 = \{p_0 > \tfrac12\}$, and in each round calls an auditor on fresh validation data to find, for each of $X$, $X_0$, $X_1$, a function $h$ correlated with the residual $p_t - y$ restricted to that set; it stops when the largest correlation $\mathbb{E}[h(x)(p_t(x) - y)]$ is at most $\alpha$, and otherwise updates $p_{t+1}(x) \propto e^{-\eta h(x)} p_t(x)$ on the chosen set (a multiplicative step in log-odds). If the auditor agnostically learns $\mathcal{C}$, of dimension $d(\mathcal{C})$, then with step size $\eta = \Theta(\alpha)$ the procedure returns a predictor that is $\alpha$-multiaccurate with respect to $\mathcal{C}$ (that is, $|\mathbb{E}[c(x)(p(x) - y)]| \le \alpha$ for $c \in \mathcal{C}$) after $T = O(\ell_D(p_0)/\alpha^2)$ rounds, using $\tilde O\big(T\,(d(\mathcal{C}) + \log(1/\delta))/\alpha^2\big)$ samples, with probability at least $1-\delta$. It does no harm on audited subgroups: if $\Pr[x \in S] \ge \gamma$, the auditor audits $\mathbf{1}_S$ and $-\mathbf{1}_S$, and $\alpha \le \beta\gamma$, then the classification error of the output on $S$ is at most $3\,\mathrm{er}_S(p_0) + 4\beta$.

## Proof sketch

For $\eta$ of order $\alpha$, each multiplicative update on the chosen set lowers the cross-entropy loss there by $\Omega(\alpha^2)$, and the loss is nonnegative, which bounds the number of rounds by $O(\ell_D(p_0)/\alpha^2)$. Uniform convergence over $\mathcal{C}$ on fresh samples in each round makes the empirical audits accurate. The do-no-harm bound follows the argument for classification error from multiaccuracy: splitting $S$ by label and by the thresholded prediction, a test correlated with the labels on $S$ that passes the audit with tolerance $\alpha \le \beta\gamma$ forces the misclassified parts of $S$ to be small, and the partition by $p_0$ relates these parts to the errors of $p_0$.

## Depends on

- [Multiaccurate predictors](multiaccurate-predictor.md)

## Sources

- M. P. Kim, A. Ghorbani, J. Zou, "Multiaccuracy: Black-Box Post-Processing for Fairness in Classification", AIES (2019), arXiv:1805.12317, Algorithm 1, Theorems 2 and 3.
