# Optimal proposal for Lambda-coalescent importance sampling in the infinitely-many-sites model

Let a sample of $n$ sequences under the infinitely-many-sites model be summarized as a genetree $(\mathbf t,\mathbf n)$: distinct types $\mathbf t_1,\dots,\mathbf t_d$ (paths of mutations to the root) with multiplicities $\mathbf n = (n_1,\dots,n_d)$, $|\mathbf n| = n$. Genealogies follow a Lambda-coalescent with merger rates $\lambda_{b,k}$ (rate at which a given $k$ of $b$ lineages merge), and mutations occur at rate $r = \theta/2$ per lineage. The block-counting process $Y$ jumps from $b$ to $b-k+1$ at rate $\binom{b}{k}\lambda_{b,k}$; write $\tilde q_b$ for its total jump rate out of $b$ and

$$
g(n,m) = \mathbb{E}_n\Big[\int_0^\infty \mathbf 1_{\{Y_s = m\}}\,ds\Big], \qquad n \ge m \ge 2,
$$

for its Green function. Let $\mathbb{P}_{\theta,n}$ be the law of the forward (in time) history $H = (H_{-\tau},\dots,H_0)$ of genetrees, from the root $((0),(1))$ to a sample of size $n$, and $G^{(n)}(\mathbf t',\mathbf n') = \mathbb{P}_{\theta,n}\{\exists\,\ell : H_\ell = (\mathbf t',\mathbf n')\}$.

**Lemma (sampling probability and Green function).** The probability $p(\mathbf t,\mathbf n)$ of observing the genetree satisfies

$$
p(\mathbf t,\mathbf n) = G^{(n)}(\mathbf t,\mathbf n)\,\frac{\tilde q_n}{nr + \tilde q_n},
$$

and for configurations of smaller size $n' < n$,

$$
p(\mathbf t',\mathbf n') = \frac{G^{(n)}(\mathbf t',\mathbf n')}{g(n,n')\,(n'r + \tilde q_{n'})}.
$$

**Lemma (optimal proposal).** Under the optimal (zero-variance) proposal $Q^*_\theta$, the time-reversed history started at $H_0 = (\mathbf t,\mathbf n)$ is a Markov chain absorbed at the root with transition probabilities

$$
Q^*_\theta\big(H_{\ell-1} = (\mathbf t',\mathbf n') \mid H_\ell = (\mathbf t'',\mathbf n'')\big) = \frac{G^{(n)}(\mathbf t',\mathbf n')}{G^{(n)}(\mathbf t'',\mathbf n'')}\;\mathbb{P}_{\theta,n}\big(H_\ell = (\mathbf t'',\mathbf n'') \mid H_{\ell-1} = (\mathbf t',\mathbf n')\big),
$$

and these transition probabilities do not depend on $n$ (as long as $n \ge |\mathbf n''|$).

Practical schemes replace the unknown ratio by approximations: the Lambda-Griffiths–Tavaré proposal, which uses the forward rates directly (removing a singleton mutation, or merging $k$ lineages of type $i$ with weight $\binom{n}{k}\lambda_{n,k}\frac{n_i-k+1}{n-k+1}$); the Lambda-Stephens–Donnelly proposal, which chooses a lineage uniformly and, for a merger, the number $k$ merging in proportion to the block-counting rate from $n$ to $n-k+1$; and proposals based on exact probabilities of compressed genetrees with one or two segregating sites, extending the approach of Hobolth, Uyenoyama and Wiuf.

## Expansion

The sampling probability equals the probability that the forward history visits $(\mathbf t,\mathbf n)$ and then the next event, at size $n$, is the stopping time of sampling rather than a mutation; this gives the factor $\tilde q_n/(nr + \tilde q_n)$, and for smaller sizes the expected time spent at size $n'$ enters through $g(n,n')$. The optimal proposal is obtained by Bayes' rule on the history: reversing the Markov chain $\mathbb{P}_{\theta,n}$ conditioned to hit the observed sample is a Doob $h$-transform with $h = G^{(n)}$, and the Green function factors cancel in the ratio, which makes the transitions independent of $n$. Each proposal then yields an unbiased estimator of $p(\mathbf t,\mathbf n)$ by weighting simulated histories by the likelihood ratio.

## Sources

- Matthias Birkner, Jochen Blath, Matthias Steinrücken, "Importance sampling for Lambda-coalescents in the infinitely many sites model", *Theoretical Population Biology* 79 (2011), 155–173, <https://doi.org/10.1016/j.tpb.2011.01.005>; preprint arXiv:1105.1836, <https://doi.org/10.48550/arXiv.1105.1836>. Numbering of the arXiv version: Section 2 (Lemmas 2.1–2.2, Definitions 2.3–2.16), Section 3 and Appendix (Green function of the block-counting process).
