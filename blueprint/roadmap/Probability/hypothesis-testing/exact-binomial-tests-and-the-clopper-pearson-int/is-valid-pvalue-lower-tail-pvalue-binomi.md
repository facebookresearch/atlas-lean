# Exact binomial test of a one-sided null p ≥ p₀

Let $\mu$ be a measure on $\Omega$, let $n \in \mathbb{N}$ and $p, p_0 \in [0,1]$ with $p_0 \le p$, and let $X : \Omega \to \mathbb{N}$ have law $\mathrm{Bin}(n,p)$ under $\mu$. A real random variable $T$ on $\Omega$ is a valid p-value under $\mu$ if $\mu\{T \le t\} \le t$ for every $t \in [0,1]$. Then the exact lower-tail p-value computed under the boundary null,

$$T(\omega) = \mathrm{Bin}(n,p_0)\big(\{j \le X(\omega)\}\big),$$

is a valid p-value under $\mu$. So the exact binomial test of the composite null hypothesis $p \ge p_0$ that rejects when $T \le t$ has size at most $t$.

## Sources

- E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005), Lemma 3.3.1.
