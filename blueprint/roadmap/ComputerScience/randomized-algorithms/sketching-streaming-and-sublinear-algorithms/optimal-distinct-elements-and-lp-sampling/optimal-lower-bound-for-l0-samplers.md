# Optimal Omega(log(1/delta) log^2(n/log(1/delta))) lower bound for L0 samplers

In the one-way public-coin communication problem *universal relation*, Alice and Bob receive $x \ne y \in \{0,1\}^n$ and Bob must output an index $i$ with $x_i \ne y_i$; write $t = \max\{1, \log_2(1/\delta)\}$ for its failure probability $\delta$, bounded away from $1$. There is an absolute constant $c \in (0, 1)$ such that its randomized public-coin one-way communication complexity is

$$
\Theta(n) \quad \text{if } t \ge cn, \qquad \Theta\Big(t \log^2\frac{n}{t}\Big) \quad \text{if } t < cn,
$$

even under the promise $\mathrm{support}(y) \subset \mathrm{support}(x)$. (Kapralov et al. write this as $\Theta(\min\{n, t\log^2(n/t)\})$; the split is needed because $\log(n/t)$ vanishes at $t = n$, for instance at $\delta = 2^{-n}$, and is negative for $t > n$.) Consequently, for every $0 \le p < 2$, every $L_p$ sampler with failure probability $\delta$ on strict turnstile streams over $[n]$ needs $\Omega(n)$ bits if $t \ge cn$ and $\Omega(t\log^2(n/t))$ bits if $t < cn$, even when $x \in \{0,1\}^n$ at all times; in particular the $O(\log^2 n)$-bit $L_0$ sampler is optimal for constant $\delta$.

## Proof sketch

A sampler with small memory solves universal relation: Alice inserts $x$, sends the memory, Bob deletes $y$, and a sample from the support of $x - y$ is a differing index. One proof turns a low-memory protocol into an encoder for subsets of $[n]$ of a fixed size: the encoder plays Alice on the set and simulates Bob on adaptively chosen subsets, revealing elements one batch at a time, and random noise injected into these adaptive queries keeps the protocol correct, so the set is encoded with fewer bits than the information-theoretic minimum, a contradiction. The second proof is a randomized reduction from augmented indexing that also interacts with the protocol adaptively, with a union bound over the likely interaction patterns. The matching upper bound follows by minor modifications of the Jowhari–Sağlam–Tardos sampler.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)
- [Approximate and perfect Lp samplers for turnstile streams](lp-samplers-in-turnstile-streams.md)
- [Jowhari-Sağlam-Tardos samplers: zero-relative-error L0 sampling in O(log^2 n) bits](l0-sampler-with-log-squared-bits.md)

## Sources

- Michael Kapralov, Jelani Nelson, Jakub Pachocki, Zhengyu Wang, David P. Woodruff, Mobin Yahyazadeh, "Optimal lower bounds for universal relation, and for samplers and finding duplicates in streams", FOCS (2017), arXiv:1704.00633, Theorem 1.
