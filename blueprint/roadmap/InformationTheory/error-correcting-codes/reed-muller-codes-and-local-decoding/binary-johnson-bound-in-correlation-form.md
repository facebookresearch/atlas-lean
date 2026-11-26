# Binary Johnson bound in sign-correlation form

Read binary words on a finite set $X$ as $\pm 1$ vectors, with sign correlation $\langle f, g \rangle = \sum_{x} (-1)^{f(x)}(-1)^{g(x)}$. Let $w$ be a word and $c_1, \dots, c_s$ ($s \ge 1$) words with $\langle c_i, w \rangle \ge \alpha|X|$ for all $i$, where $\alpha \ge 0$, and $\langle c_i, c_j \rangle \le \beta|X|$ for all $i \ne j$. Then

$$s\,(\alpha^2 - \beta) \le 1 - \beta.$$

In particular, if distinct codewords agree on at most a $1/2 + \varepsilon^2$ fraction of positions, then fewer than $1/(2\varepsilon^2)$ codewords agree with any $w$ on at least a $1/2 + \varepsilon$ fraction. More generally, if messages farther than $r$ apart have encodings with correlation at most $2\varepsilon^2|X|$ and every radius-$r$ ball holds at most $V$ messages, then at most $V/(2\varepsilon^2)$ messages have encodings agreeing with $w$ on a $1/2 + \varepsilon$ fraction.

## Proof sketch

Apply Cauchy-Schwarz to $w$ and $\sum_i c_i$: the inner product is at least $s\alpha|X|$, and the squared norm of the sum is at most $s|X| + s(s - 1)\beta|X|$. Rearranging gives the inequality; agreement on a $1/2 + \varepsilon$ fraction means correlation at least $2\varepsilon|X|$, so take $\alpha = 2\varepsilon$, $\beta = 2\varepsilon^2$. The covering version applies this to a maximal set of pairwise far messages.

## Depends on

- [Johnson bound](../list-decoding/johnson-bound.md)
- [List-decodable code](../list-decoding/is-list-decodable.md)

## Proof depends on

- [Local decoding of the Hadamard code](../hadamard-code-local-decoding.md)

## Sources

- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.
- M. Sudan, L. Trevisan, S. Vadhan, "Pseudorandom Generators without the XOR Lemma", Journal of Computer and System Sciences, 2001.
