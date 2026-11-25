# Bounded-distance decoding error over a binary symmetric channel

Let $n, k, t \in \mathbb{N}$, let $\mathrm{enc} : \mathbb{F}_2^k \to \mathbb{F}_2^n$ and $\mathrm{dec} : \mathbb{F}_2^n \to \mathbb{F}_2^n$ be maps such that $\mathrm{dec}(\mathrm{enc}(x) + e) = \mathrm{enc}(x)$ for every message $x$ and every error word $e$ of Hamming weight $|e| \le t$. Let $0 \le \delta \le 1$ and let $\mu_\delta$ be the binary symmetric channel law on $\mathbb{F}_2^n$, the product of $n$ independent Bernoulli($\delta$) flips. Then for every message $m \in \mathbb{F}_2^k$,

$$\mu_\delta\{e : \mathrm{dec}(\mathrm{enc}(m) + e) \ne \mathrm{enc}(m)\} \le \operatorname{binomTail}(n, t+1, \delta),$$

where

$$\operatorname{binomTail}(n, k, \delta) = \sum_{i=k}^{n} \binom{n}{i} \delta^i (1-\delta)^{n-i}$$
