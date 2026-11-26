# Universal hashing isolates preimages and bounds the remaining entropy

Let $(h_s)_s$ be a hash family $\mathrm{In} \to \mathrm{Out}$ with seed $s$ drawn from a distribution such that $\Pr_s[h_s(x) = h_s(y)] \le 1/|\mathrm{Out}|$ for all $x \ne y$, and let $f : \mathrm{In} \to \mathrm{Im}$ be a function on finite sets. For every $x$, the probability over $s$ that some $y \ne x$ with $f(y) = f(x)$ has $h_s(y) = h_s(x)$ is at most $\min\big(1, (|f^{-1}(f(x))| - 1)/|\mathrm{Out}|\big)$. Consequently, for $x \sim p$ and every predicate $\phi(s, x) \in \{0,1\}$,

$$
H\big(\phi(s, x) \,\big|\, s, f(x), h_s(x)\big) \le \sum_x p(x)\min\Big(1, \frac{|f^{-1}(f(x))| - 1}{|\mathrm{Out}|}\Big)
$$

in bits. If for each length $\ell \in \{1, \dots, L\}$ a universal family with $\ell$ output bits is used, the average over $\ell$ of these conditional entropies is at most $\big(\mathbb{E}_{x\sim p}[\log_2|f^{-1}(f(x))|] + 2\big)/L$.

## Proof sketch

The isolation bound is a union bound over the competitors of $x$ in its fiber. When $x$ is isolated, $(s, f(x), h_s(x))$ determines $x$ and hence $\phi(s,x)$, so a bit has conditional entropy at most the probability of non-isolation. For the averaged bound, the non-isolation term with $\ell$ bits is $\min(1, (N - 1)2^{-\ell})$ for fiber size $N$; summing over $\ell$ gives at most $\log_2 N + 2$.

## Depends on

- [Universal hash family](../../../ComputerScience/data-structures/hashing/universal-hashing/is-universal.md)
- [Conditional entropy of a finite joint law](../../entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography Conference (TCC), 2006.
