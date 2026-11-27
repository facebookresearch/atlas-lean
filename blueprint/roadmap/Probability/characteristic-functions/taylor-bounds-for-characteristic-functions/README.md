# Taylor bounds for characteristic functions

Let $X$ be a measurable real random variable on a probability space with $\mathbb{E}[X^2]$ finite, and let $\varphi_X(t) = \mathbb{E}[e^{itX}]$ be the characteristic function of its law. Then for every real $t$, $|\varphi_X(t) - 1 - it \, \mathbb{E}[X]| \le t^2 \, \mathbb{E}[X^2]$.

## Idea

The bound is the expectation of a pointwise inequality for the exponential: $|e^{iu} - 1 - iu| \le u^2$ for every real $u$, with no smallness condition on $u$. Putting $u = tX$, taking expectations and using $|\mathbb{E}[Z]| \le \mathbb{E}|Z|$ gives the statement. It makes precise that a characteristic function is $1 + it\,\mathbb{E}[X] + O(t^2)$ near $0$, and for a centred variable it reads $|\varphi_X(t) - 1| \le t^2 \, \mathbb{E}[X^2]$, which is how proofs of the central limit theorem show that $\varphi_X(t/\sqrt{n})$ is close to $1$. The first-order bound $|\varphi_X(t) - 1| \le |t| \, \mathbb{E}|X|$ comes the same way from $|e^{iu} - 1| \le |u|$. The constant is not optimal: the sharper inequality $|e^{iu} - 1 - iu| \le u^2/2$ halves it.

## Statements

- [Second-order Taylor bound for the characteristic function](norm-char-fun-sub-one-sub-le.md)
- [First-order Taylor bound for the characteristic function](norm-char-fun-sub-one-le.md): first-order bound
- [Characteristic-function second-order bound](norm-char-fun-sub-one-le-sq-mul-variance.md): consequence in terms of the variance
- [Global second-order bound for the imaginary exponential](norm-exp-of-real-mul-i-sub-one-sub-le.md): lemma used in the proof of the main statement
