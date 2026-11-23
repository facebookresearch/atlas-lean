# Backwards martingale

Let $\mu$ be a measure on a measurable space $(\Omega, \mathcal F)$
and let $(\mathcal F_n)_{n \ge 0}$ be a sequence of σ-algebras on $\Omega$. A sequence of
functions $M_n : \Omega \to \mathbb R$ is a backwards martingale with respect to $(\mathcal F_n)$
and $\mu$ if $M_0$ is $\mu$-integrable and, for every $n$, $M_n = \mathbb E[M_0 \mid \mathcal F_n]$
$\mu$-almost everywhere.

Here $\mathbb E[M_0 \mid \mathcal F_n]$ is the conditional expectation with respect to $\mu$ when
$\mathcal F_n \subseteq \mathcal F$ and the restriction of $\mu$ to $\mathcal F_n$ is σ-finite,
and is $0$ by convention otherwise. The definition is used when $(\mathcal F_n)$ is a decreasing
sequence of sub-σ-algebras, but it does not require this.
