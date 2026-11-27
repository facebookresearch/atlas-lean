# Optimal Omega(log(1/delta) log^2(n/log(1/delta))) lower bound for L0 samplers

In the one-way public-coin communication problem *universal relation*, Alice and Bob receive $x \ne y \in \{0,1\}^n$ and Bob must output an index $i$ with $x_i \ne y_i$; its randomized one-way communication complexity with failure probability $\delta$ is exactly

$$
\Theta\Big(\min\Big\{n, \; \log(1/\delta)\log^2\frac{n}{\log(1/\delta)}\Big\}\Big),
$$

even under the promise $\mathrm{support}(y) \subset \mathrm{support}(x)$. Consequently, for every $0 \le p < 2$, every $L_p$ sampler with failure probability $\delta$ on strict turnstile streams over $[n]$ needs $\Omega(\min\{n, \log(1/\delta)\log^2(n/\log(1/\delta))\})$ bits, even when $x \in \{0,1\}^n$ at all times; in particular the $O(\log^2 n)$-bit $L_0$ sampler is optimal for constant $\delta$.

## Proof sketch

A sampler with small memory solves universal relation: Alice inserts $x$, sends the memory, Bob deletes $y$, and a sample from the support of $x - y$ is a differing index. One proof turns a low-memory sampler into an adaptive encoder for subsets of $[n]$ of prescribed sizes: repeatedly querying samples and deleting recovered elements reveals the set with fewer bits than its entropy, a contradiction. The second proof reduces from augmented indexing over $\log(n/\log(1/\delta))$ scales, each contributing a $\log$ factor.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)
- [Approximate and perfect Lp samplers for turnstile streams](lp-samplers-in-turnstile-streams.md)

## Proof depends on

- [Yao's minimax principle for communication complexity](../../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity-eq-i-sup-dist-complexity.md)
- [Jowhari-Sağlam-Tardos samplers: zero-relative-error L0 sampling in O(log^2 n) bits](l0-sampler-with-log-squared-bits.md)

## Sources

- Michael Kapralov, Jelani Nelson, Jakub Pachocki, Zhengyu Wang, David P. Woodruff, Mobin Yahyazadeh, "Optimal lower bounds for universal relation, and for samplers and finding duplicates in streams", FOCS (2017), arXiv:1704.00633.
