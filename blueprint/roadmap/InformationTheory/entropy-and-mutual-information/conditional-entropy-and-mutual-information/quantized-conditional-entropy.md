# Conditional entropy of a finite observation given a sub-$\sigma$-algebra

Let $\mu$ be a
probability measure on a measurable space $\Omega$, let $m$ be a sub-$\sigma$-algebra of the
$\sigma$-algebra of $\Omega$, let $n \in \mathbb{N}$, and let $f : \Omega \to \{0, \dots, n-1\}$ be
measurable. For each $i < n$ let $P_i = \mathbb{E}_\mu[\mathbf{1}_{\{f = i\}} \mid m]$ be the
conditional probability of $\{f = i\}$ given $m$. The quantized conditional entropy of $f$ given
$m$, in bits, is

$$H_\mu(f \mid m) = \int_\Omega \sum_{i < n} -P_i(\omega) \log_2 P_i(\omega) \, d\mu(\omega),$$

with the convention $0 \log_2 0 = 0$.
