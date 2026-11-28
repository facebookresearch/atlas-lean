# Fisher-Shannon number of cardinality sketches: PCSA, HyperLogLog and Fishmonger

Model a mergeable cardinality sketch $A$ in the random oracle model, after Poissonization, by the law of its random state $X_{A,\lambda}$ at true cardinality $\lambda > 0$, with Shannon entropy $H(X_{A,\lambda})$, in bits, and Fisher information $I_A(\lambda)$ about $\lambda$. For a base $q > 1$, $A$ is *weakly scale-invariant with base $q$* if $H(X_{A,q\lambda}) = H(X_{A,\lambda})$ and $I_A(\lambda) = q^2 I_A(q\lambda)$ for every $\lambda > 0$; then the entropy and the normalized information $\lambda^2 I_A(\lambda)$ are periodic functions of $\log_q \lambda$ that need not be constant (for LogLog-type sketches they oscillate). Its *Fisher–Shannon number* is $\mathcal{H}/\mathcal{I}$, where $\mathcal{H} = \int_0^1 H(X_{A,q^r})\,dr$ and $\mathcal{I} = \int_0^1 q^{2r} I_A(q^r)\,dr$ are the averages of the entropy and of the normalized information over one period. Combining $m$ copies of $A$ with independent uniformly random offsets $R_1, \dots, R_m \in [0, 1)$ (the $i$-th copy sees cardinality $\lambda q^{-R_i}$) and observing each copy as the pair $(R_i, Y_i)$ of its offset and its state, Lemmas 1 and 2 give, for every $\lambda$, Fisher information $I_{(R_i, Y_i)}(\lambda) = \mathcal{I}/\lambda^2$ of each pair and conditional entropy $H(Y_i \mid R_i) = \mathcal{H}$, the entropy of the state given the offset averaged over $R_i$; these are not the information $I_{Y_i}(\lambda)$ and entropy $H(Y_i)$ of the state alone. Consequently, under the regularity conditions of the Cramér–Rao bound (Section 2.3: the support of the state law does not depend on $\lambda$, and the differentiations involved are permitted), every unbiased estimator of $\lambda$ from the $m$ pairs has relative variance at least $1/(m\mathcal{I})$, while any encoding of the $m$ states for a decoder that knows the offsets has expected length at least $m\mathcal{H}$. So a sketch of $m$ such offset copies with an unbiased estimator of relative standard error $1/\sqrt{b}$ has expected encoded length at least $(\mathcal{H}/\mathcal{I})\,b$ bits (Section 3.4). This bounds the expected coded length, not the worst-case space, and it says nothing about biased estimators, whose variance can be made smaller by scaling. As $m \to \infty$, an asymptotically efficient estimator (asymptotically unbiased with relative variance $(1 + o(1))/(m\mathcal{I})$, such as the maximum likelihood estimator) and compression to the conditional entropy attain it. There are explicit constants $H_0, I_0$ with $H_0/I_0 \approx 1.98016$ such that:

1. every base-$q$ variant of Flajolet–Martin's PCSA sketch has Fisher–Shannon number exactly $H_0/I_0$, and every base-$q$ variant of HyperLogLog has a strictly larger number, tending to $H_0/I_0$ as $q \to \infty$;
2. the sketch *Fishmonger*, on multisets over a universe $[U]$ with $m = \omega(\log^2\log U)$, uses at all times and with high probability $(1 + o(1))(H_0/I_0)\,m \approx 1.98\,m$ bits and has standard error $1/\sqrt{m}$;
3. no *linearizable* sketch (a natural class containing the popular mergeable sketches) has Fisher–Shannon number below $H_0/I_0$.

## Proof sketch

For PCSA-type and LogLog-type sketches the state is a vector of independent geometric-like registers, so both entropy and Fisher information are explicit series in the base $q$, computed after Poissonizing the insertion process and averaged over one period of $\log_q \lambda$. Fishmonger smooths PCSA's estimator and stores its state with an entropy coder, achieving the entropy bound. The lower bound for linearizable sketches compares, for every sketch in the class, its limiting entropy with its Fisher information and shows that the ratio cannot fall below the value attained by PCSA.

## Depends on

- [Fisher information](../../../../Probability/statistical-estimation/fisher-information-and-the-cram-r-rao-bound/fisher-information.md)
- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)

## Proof depends on

- [Cramér–Rao inequality](../../../../Probability/statistical-estimation/fisher-information-and-the-cram-r-rao-bound/cramer-rao.md)

## Sources

- Seth Pettie, Dingyu Wang, "Information Theoretic Limits of Cardinality Estimation: Fisher Meets Shannon", STOC (2021), arXiv:2007.08051, Sections 2.3 and 3.4, Definitions 2 and 3, Lemmas 1 and 2.
