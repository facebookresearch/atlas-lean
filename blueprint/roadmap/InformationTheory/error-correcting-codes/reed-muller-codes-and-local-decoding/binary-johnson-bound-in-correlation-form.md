# Binary Johnson bound in sign-correlation form

Read binary words of length $n$ as $\pm 1$ vectors, with sign correlation $\langle f, g \rangle = \sum_{i=1}^{n} (-1)^{f_i}(-1)^{g_i}$, so that $\langle f, g\rangle = n - 2\Delta(f, g)$ for the Hamming distance $\Delta$. Let $w$ be a word and $c_1, \dots, c_s$ distinct words with $\langle c_i, c_j \rangle \le \beta n$ for all $i \ne j$ and $\langle c_i, w \rangle \ge \alpha n$ for all $i$, where $\alpha^2 > \beta$. Then

$$s \le \frac{1 - \beta}{\alpha^2 - \beta}.$$

In particular, if an error-correcting code $E : \{0,1\}^k \to \{0,1\}^n$ has relative distance at least $1/2 - \varepsilon$, then for every word $w$ and every $\delta \ge \sqrt{\varepsilon}$ there are at most $1/(2\delta^2)$ codewords within relative distance $1/2 - \delta$ of $w$.

## Proof sketch

The first bound is the binary case of the Johnson bound in averaged form: for a set $B$ of words with average pairwise distance $d$ and average distance $e$ from $w$, $|B| \le (2d/n)/\big((1 - 2e/n)^2 - (1 - 2d/n)\big)$ whenever the denominator is positive. In correlation terms the average pairwise correlation is $b = 1 - 2d/n \le \beta$ and the average correlation with $w$ is $a = 1 - 2e/n \ge \alpha$, and $(1 - b)/(a^2 - b)$ is increasing in $b$ and decreasing in $a$. A direct proof applies Cauchy-Schwarz to $w$ and $\sum_i c_i$: the inner product is at least $s\alpha n$ and the squared norm of the sum is at most $sn + s(s - 1)\beta n$. The "In particular" clause is the case $\alpha = 2\delta$, $\beta = 2\varepsilon \le 2\delta^2$, where the same computation gives $4\delta^2 s^2 \le s + 2s^2\delta^2$.

The following forms are derived here and are not stated in the cited sources. The inequality $s(\alpha^2 - \beta) \le 1 - \beta$ holds for every $\alpha \ge 0$ (if $\alpha^2 \le \beta$ the left side is at most $0$). If messages farther than $r$ apart have encodings with correlation at most $2\varepsilon^2 n$ and every radius-$r$ ball holds at most $V$ messages, then at most $V/(2\varepsilon^2)$ messages have encodings agreeing with $w$ on a $1/2 + \varepsilon$ fraction: apply the bound to a maximal set of pairwise far such messages and cover the rest by radius-$r$ balls around it.

## Depends on

- [Johnson bound](../list-decoding/johnson-bound.md)
- [List-decodable code](../list-decoding/is-list-decodable.md)

## Proof depends on

- [Local decoding of the Hadamard code](../hadamard-code-local-decoding.md)

## Sources

- V. Guruswami, "Algorithmic Results in List Decoding", Foundations and Trends in Theoretical Computer Science 2(2), 2006, Section 3.1, Theorem 3.1 and Corollary 3.2 (case $q = 2$).
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009; web draft of January 2007, Section 17.7, Theorem 17.26 (Johnson Bound).
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.
- M. Sudan, L. Trevisan, S. Vadhan, "Pseudorandom Generators without the XOR Lemma", Journal of Computer and System Sciences, 2001.
