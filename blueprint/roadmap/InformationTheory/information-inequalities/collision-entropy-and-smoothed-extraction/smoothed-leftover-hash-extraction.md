# Leftover hashing from concentrated conditional entropy

For bit strings $a, x$ of length $N$ let $ax$ be their product in $\mathrm{GF}(2^N)$ (in a fixed representation), let $z|_\lambda$ be the first $\max(\lfloor \lambda \rfloor, 0)$ bits of a string $z$, let $\|$ be concatenation, and let $\mathrm{Ext}_\lambda(x, a) = (ax)|_\lambda \,\|\, a$. Let $P_{XY}$ be a joint law on finite sets $\mathcal{X} \times \mathcal{Y}$ with $\mathcal{X} \subseteq \{0,1\}^n$, let $(X_1, Y_1), \dots, (X_k, Y_k)$ be i.i.d. according to $P_{XY}$, and let $A$ be uniform on $\{0,1\}^{kn}$ and independent of them (so $N = kn$ in $\mathrm{Ext}$). Let $\varepsilon \in (0, 1)$ with $k > \log_2(1/\varepsilon)$, and put

$$
\lambda = k\,H(X \mid Y) - 8 \log_2|\mathcal{X}|\,\sqrt{k \log_2(1/\varepsilon)}.
$$

Then the joint law of $\big(\mathrm{Ext}_\lambda(X_1 \| \cdots \| X_k,\ A),\ Y_1 \| \cdots \| Y_k\big)$ is within statistical distance $\varepsilon$ of $U \times P_Y^{k}$, where $U$ is an independent uniform bit string of length $\max(\lfloor \lambda \rfloor, 0) + kn$.

## Proof sketch

Concentration of conditional information gives a distribution within statistical distance $2\varepsilon'$ of the samples whose conditional min-entropy is at least $kH(X \mid Y) - 6\sqrt{k\log_2(1/\varepsilon')}\log_2|\mathcal{X}|$, and the leftover hash lemma for the multiplication family, applied for each value of the side information, makes the truncated product $2\varepsilon''$-close to uniform after dropping $2\log_2(1/\varepsilon'')$ further bits; choosing $\varepsilon', \varepsilon''$ as fixed fractions of $\varepsilon$ gives the stated loss.

The following smoothing forms for an arbitrary hash family are derived here and are not stated in the cited sources. Let $(h_s)$ be a family into a finite set $\mathrm{Out}$ with $\Pr_s[h_s(x) = h_s(x')] \le 1/|\mathrm{Out}|$ for $x \ne x'$. (1) For a source $p$ and $m \ge 0$, the statistical distance between $(s, h_s(x))$ with $x \sim p$ and $(s, u)$ with $u$ uniform is at most $2\Pr_p[p(x) > m] + \frac12\sqrt{2m|\mathrm{Out}|}$: conditioning the source on light outcomes changes it by at most the heavy probability on each side and leaves masses at most $2m$ after renormalization (when the heavy probability is at most $1/2$; otherwise the bound is trivial), so the collision-probability form of the leftover hash lemma applies; with public side information only the average probability of heavy conditional outcomes is charged. (2) For independent pairs $(Y_i, X_i)_{i \in I}$ with positive masses at least $2^{-B}$, hashing the tuple $X = (X_i)$ gives, for every $\varepsilon \ge 0$, a joint law of $((Y_i)_i, s, h_s(X))$ within statistical distance $2\exp(-2\varepsilon^2/(|I|B^2)) + \frac12\sqrt{2|\mathrm{Out}|\,2^{-(\sum_i H(X_i \mid Y_i) - \varepsilon)}}$ of $((Y_i)_i, s, u)$, by the Hoeffding form of concentration of conditional information at threshold $2^{-(\sum_i H(X_i \mid Y_i) - \varepsilon)}$.

## Depends on

- [Conditional entropy of a finite joint law](../../entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)
- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Leftover hash lemma with side information](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma-with-side-information.md)
- [Universal hash family](../../../ComputerScience/data-structures/hashing/universal-hashing/is-universal.md)
- [Concentration of conditional information in independent samples](concentration-of-conditional-information.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography Conference (TCC), 2006, Section 3.3, Lemma 2 (with Lemma 1, Proposition 1 and the notation of Section 3.1).
- S. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012.
