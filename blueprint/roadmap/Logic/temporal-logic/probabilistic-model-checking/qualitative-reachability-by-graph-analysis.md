# Qualitative reachability by graph analysis

Let $M$ be a finite [Markov decision process](markov-decision-processes-and-adversaries.md) with target set $T$, and say that $s \to s'$ under $a$ if $\delta(s, a)(s') > 0$. The [qualitative sets](extremal-reachability-probabilities.md) are computed by fixed-point iterations that use only which transitions have positive probability:

- $S^0_{\max} = S \setminus R$, where $R$ is the least set containing $T$ and every state with some action leading into $R$;
- $S^0_{\min} = S \setminus R$, where $R$ is the least set containing $T$ and every state all of whose actions can lead into $R$;
- $S^1_{\min}$ is the greatest subset $R$ of $S \setminus S^0_{\min}$ such that no state of $R \setminus T$ has an action that can leave $R$ (states of $T$ may have any actions, since a path that starts in $T$ has already reached it);
- $S^1_{\max}$ is the greatest set $R'$ such that $R'$ equals the least set $R$ containing $T$ and every state with an action all of whose successors lie in $R'$ and at least one of which lies in $R$.

## Depends on

- [Extremal reachability probabilities](extremal-reachability-probabilities.md)
- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 4.1, Algorithms 1–4.
