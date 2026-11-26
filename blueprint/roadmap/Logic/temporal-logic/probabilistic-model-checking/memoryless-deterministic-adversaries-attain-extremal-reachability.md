# Memoryless deterministic adversaries attain extremal reachability probabilities

For every finite [Markov decision process](markov-decision-processes-and-adversaries.md) and every set $T$ of target states there are deterministic memoryless adversaries $\sigma_{\min}$ and $\sigma_{\max}$ that attain the [extremal reachability probabilities](extremal-reachability-probabilities.md) simultaneously from every state: $\Pr^{\sigma_{\min}}_{M,s}(\mathit{reach}_s(T)) = \Pr^{\min}_s(\mathit{reach}(T))$ and $\Pr^{\sigma_{\max}}_{M,s}(\mathit{reach}_s(T)) = \Pr^{\max}_s(\mathit{reach}(T))$ for all states $s$. In particular the infimum and supremum over all adversaries are a minimum and a maximum. For the minimum, $\sigma_{\min}(s)$ may be any action minimizing $\sum_{s'} \delta(s, a)(s') \Pr^{\min}_{s'}(\mathit{reach}(T))$. For the maximum, choosing a maximizing action in each state does not suffice in general; value iteration can be adapted to build $\sigma_{\max}$ by changing the action of a state only when its value strictly improves.

## Depends on

- [Extremal reachability probabilities](extremal-reachability-probabilities.md)
- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 4 (the statement that deterministic memoryless adversaries achieve the minimum and maximum probabilities) and Section 4.3 (adversary generation).
