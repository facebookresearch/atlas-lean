# One-step recursion for survival mass

Let $q$ assign to each finite prefix of tokens from a finite alphabet a distribution on the next symbol, an ordinary token or end of sequence. For $n \in \mathbb N$ the survival mass at horizon $n + 1$ satisfies

$$s_{n+1}(q) = \sum_a q_{\varnothing}(a)\, s_n(q^{(a)}),$$

where $q_{\varnothing}(a)$ is the probability that the first symbol is the token $a$, $q^{(a)}(w) = q(a\,w)$ is the kernel shifted by $a$, and $s_0 = 1$.
