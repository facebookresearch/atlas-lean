# Universal hashing isolates preimages and bounds the remaining entropy

Let $f : \{0,1\}^n \to \{0,1\}^m$ be a function. For bit strings $a, x$ of length $n$ let $ax$ be their product in $\mathrm{GF}(2^n)$ (in a fixed representation), let $z|_i$ be the first $i$ bits of a string $z$, and let $x \odot r = \bigoplus_j x_j r_j$ be the inner product. Define

$$
g(x, i, a, r) = f(x)\,\|\,i\,\|\,a\,\|\,(ax)|_i\,\|\,r, \qquad P(x, i, a, r) = x \odot r,
$$

where $\|$ is concatenation, and let $W = (X, I, A, R)$ with $X, A, R$ uniform on $\{0,1\}^n$ and $I$ uniform on $\{1, \dots, n\}$, all independent. Then for $y = f(x)$ and $i > \log_2|f^{-1}(y)|$, the probability over $a$ that $x$ is not determined by the output of $g$ is at most $2^{-(i - \log_2|f^{-1}(y)|)}$, and

$$
H\big(P(W) \mid g(W)\big) \le \frac{\mathbb{E}_{x}\big[\log_2|f^{-1}(f(x))|\big] + 2}{n}
$$

in bits, where $x$ is uniform on $\{0,1\}^n$.

## Proof sketch

For $x \ne x'$ the truncated products collide with probability $\Pr_a[(ax)|_i = (ax')|_i] = 2^{-i}$, and a union bound over the other preimages of $y$ gives the isolation bound. When $x$ is isolated, $g(W)$ determines $x$ and hence $P(W)$, so the conditional entropy of the bit given $f(X) = y$ and $I = i$ is at most $2^{-(i - \log_2|f^{-1}(y)|)}$; it is at most $1$ in any case. Averaging over $i$ (at most $\log_2|f^{-1}(y)|$ values with the trivial bound and a geometric series for the rest) and then over $x$ gives the averaged bound.

The following forms for an arbitrary hash family are derived here and are not stated in the cited source. Let $(h_s)_s$ be a family $\mathrm{In} \to \mathrm{Out}$ with $\Pr_s[h_s(x) = h_s(x')] \le 1/|\mathrm{Out}|$ for $x \ne x'$, and $f : \mathrm{In} \to \mathrm{Im}$ a function on finite sets. For every $x$, the probability over $s$ that some $x' \ne x$ with $f(x') = f(x)$ has $h_s(x') = h_s(x)$ is at most $\min\big(1, (|f^{-1}(f(x))| - 1)/|\mathrm{Out}|\big)$. Consequently, for $x \sim p$ and every predicate $\phi(s, x) \in \{0, 1\}$, $H(\phi(s, x) \mid s, f(x), h_s(x)) \le \sum_x p(x) \min\big(1, (|f^{-1}(f(x))| - 1)/|\mathrm{Out}|\big)$, and if for each $\ell \in \{1, \dots, L\}$ a family with $\ell$ output bits is used, the average over $\ell$ of these conditional entropies is at most $\big(\mathbb{E}_{x \sim p}[\log_2|f^{-1}(f(x))|] + 2\big)/L$, since $\sum_{\ell} \min(1, (N - 1)2^{-\ell}) \le \log_2 N + 2$.

## Depends on

- [Conditional entropy of a finite joint law](../../entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)

## Proof depends on

- [Universal hash family](../../../ComputerScience/data-structures/hashing/universal-hashing/is-universal.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography Conference (TCC), 2006, Section 3.1, equation (1), and Section 4, equations (4) and (5) and Lemma 3 with its proof.
