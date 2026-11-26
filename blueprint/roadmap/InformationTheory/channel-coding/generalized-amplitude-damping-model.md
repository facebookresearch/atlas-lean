# Generalized amplitude-damping Kraus channel and finite codes

Use positive semidefinite complex density matrices with trace one. For parameters $0\le\gamma,\nu\le1$, use four matrices $\sqrt{1-\nu}\operatorname{diag}(1,\sqrt{1-\gamma})$, $\sqrt{\gamma(1-\nu)}|0\rangle\langle1|$, $\sqrt\nu\operatorname{diag}(\sqrt{1-\gamma},1)$ and $\sqrt{\gamma\nu}|1\rangle\langle0|$. At $n$ uses the Kraus matrices are their ordered tensor products, and the channel sums conjugation by all of them. Entropy is the spectral sum of $-t\log t$ with zero summands at zero. The Holevo quantity is the supremum of the entropy of the mean output minus the mean output entropy, in bits, over finite probability ensembles. A length-$n$ code has one input state per message and a decoding POVM; the error is one minus the mean Born probability of the correct outcome under uniform messages. A rate $R$ is achievable if a sequence of such codes has error tending to zero and, for every $\varepsilon>0$, eventually $\log_2(\text{messages})/n\ge R-\varepsilon$. Capacity is the real supremum of these rates.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/AmplitudeDamping.lean#L13-L84)
