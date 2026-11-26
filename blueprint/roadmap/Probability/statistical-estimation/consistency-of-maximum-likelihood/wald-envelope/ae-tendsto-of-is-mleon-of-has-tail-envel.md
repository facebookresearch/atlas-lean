# Consistency of the MLE on a closed parameter set

Let $\Theta$ be a proper metric space (such as $\mathbb R^d$), $P$ a probability measure, $S \subseteq \Theta$ closed, and $X_0, X_1, \dots$ pairwise independent and identically distributed. Assume:

- $\theta_0 \in S$ is the unique maximizer on $S$ of $Q(\theta) = \mathbb E\,\ell(\theta, X_0)$, $\ell(\theta_0, \cdot)$ is measurable, and $\ell(\theta, X_0)$ is integrable for every $\theta \in S$;
- local envelopes at every $\theta \in S \setminus \{\theta_0\}$: measurable $u_n$, decreasing in $n$ with $u_n \to \ell(\theta, \cdot)$ pointwise, $\ell(\theta', \cdot) \le u_n$ for all $\theta' \in S$ with $d(\theta', \theta) < 1/(n+1)$, and $u_0(X_0)$ integrable;
- an envelope at infinity around some $\theta_c$: measurable $v_n$, decreasing in $n$ with $v_n \to -\infty$ pointwise, $\ell(\theta, \cdot) \le v_n$ for all $\theta \in S$ with $d(\theta, \theta_c) > n$, and $v_0(X_0)$ integrable.

Then every maximum-likelihood estimator on $S$ (maximizing $\frac1n\sum_{i<n}\ell(\theta, X_i)$ over $S$) converges to $\theta_0$ almost surely. $S$ need not be compact.
