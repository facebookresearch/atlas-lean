# The Morris approximate counter

The *Morris counter* approximately counts the number $n$ of tokens in a stream. It keeps one integer $x$, initially $0$. On each token, it increments $x$ with probability $2^{-x}$, independently of the past. Its estimate is $\hat n = 2^x - 1$.

**Theorem.** Let $C_n = 2^x$ after $n$ tokens. Then:
1. $\mathbb{E}[C_n] = n + 1$, so $\hat n$ is an unbiased estimator of $n$;
2. $\operatorname{Var}[C_n] = n(n - 1)/2$;
3. combining independent copies by the median of means gives an estimate within a factor $1 \pm \varepsilon$ with probability at least $1 - \delta$, using $O(\varepsilon^{-2}\log(1/\delta) \log\log m)$ bits for streams of length at most $m$.

**Proof.** Let $Z_i$ indicate that the counter grows on token $i + 1$. Given $C_i$, $Z_i$ is Bernoulli with mean $1/C_i$, and $C_{i+1} = (1 + Z_i) C_i$.
- $\mathbb{E}[C_{i+1}] = \mathbb{E}[(1 + 1/C_i) C_i] = \mathbb{E}[C_i] + 1$.
- $\mathbb{E}[C_{i+1}^2] = \mathbb{E}[(1 + 3Z_i)C_i^2] = \mathbb{E}[C_i^2] + 3\mathbb{E}[C_i] = \mathbb{E}[C_i^2] + 3(i + 1)$.

With $C_0 = 1$, this gives $\mathbb{E}[C_n] = n + 1$ and $\mathbb{E}[C_n^2] = 1 + 3n(n + 1)/2$, whose difference from $(n + 1)^2$ is $n(n - 1)/2$. For part 3, the variance is $O(n^2)$, so averaging $O(\varepsilon^{-2})$ copies and taking the median of $O(\log(1/\delta))$ such averages works. Aborting a copy if $x$ exceeds $2\log m$, an event of small probability by Markov's inequality, keeps each copy within $O(\log\log m)$ bits.

## Sources

- A. Chakrabarti, *Data Stream Algorithms*, lecture notes, Dartmouth College (update of 1 July 2025), <https://www.cs.dartmouth.edu/~ac/Teach/data-streams-lecnotes.pdf>, Unit 4: Algorithm 5 (the Morris counter), Algorithm 6 (the equivalent doubling formulation), Lemma 4.3.1 ($\mathbb{E} C_n = n + 1$ and $\operatorname{Var} C_n = n(n - 1)/2$, with proof), Lemma 4.4.1 (median of means), and Theorem 4.4.2 (an $(\varepsilon, \delta)$-approximation in $O(\varepsilon^{-2}\log\delta^{-1}\log\log m)$ bits).
