# Fisher-Shannon number of cardinality sketches: PCSA, HyperLogLog and Fishmonger

Model a mergeable cardinality sketch in the random oracle model as a random state $S_\lambda$ whose law depends on the true cardinality $\lambda$. Its *Fisher–Shannon number* is $\mathcal{H}/\mathcal{I}$, where $\mathcal{H}$ is the limiting Shannon entropy of the state (bits needed to store it after optimal compression) and $\mathcal{I}$ is its normalized Fisher information about $\log\lambda$; a sketch with $m$ units of Fisher information has standard error $(1 + o(1))/\sqrt{m}$ under an asymptotically efficient estimator and needs $(1 + o(1))(\mathcal{H}/\mathcal{I})\,m$ bits. There are explicit constants $H_0, I_0$ with $H_0/I_0 \approx 1.98016$ such that:

1. every base-$q$ variant of Flajolet–Martin's PCSA sketch has Fisher–Shannon number exactly $H_0/I_0$, and every base-$q$ variant of HyperLogLog has a strictly larger number, tending to $H_0/I_0$ as $q \to \infty$;
2. the sketch *Fishmonger*, on multisets over a universe $[U]$ with $m = \omega(\log^2\log U)$, uses at all times and with high probability $(1 + o(1))(H_0/I_0)\,m \approx 1.98\,m$ bits and has standard error $1/\sqrt{m}$;
3. no *linearizable* sketch (a natural class containing the popular mergeable sketches) has Fisher–Shannon number below $H_0/I_0$.

## Proof sketch

For PCSA-type and LogLog-type sketches the state is a vector of independent geometric-like registers, so both entropy and Fisher information are explicit series in the base $q$ whose limits are computed after Poissonizing the insertion process. Fishmonger smooths PCSA's estimator and stores its state with an entropy coder, achieving the entropy bound. The lower bound for linearizable sketches compares, for every sketch in the class, its limiting entropy with its Fisher information and shows that the ratio cannot fall below the value attained by PCSA.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)

## Sources

- Seth Pettie, Dingyu Wang, "Information Theoretic Limits of Cardinality Estimation: Fisher Meets Shannon", STOC (2021), arXiv:2007.08051.
