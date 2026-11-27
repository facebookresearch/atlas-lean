# Extremal reachability probabilities

Let $M$ be a [Markov decision process](markov-decision-processes-and-adversaries.md) with states $S$ and let $T \subseteq S$ be a set of target states. For a state $s$, $\mathit{reach}_s(T)$ is the set of infinite paths from $s$ that contain a state of $T$; it is measurable, as the countable union of the cylinders of the finite paths from $s$ that end in $T$. The *minimum* and *maximum reachability probabilities* are

$$\Pr^{\min}_{s}(\mathit{reach}(T)) = \inf_{\sigma} \Pr^\sigma_{M,s}(\mathit{reach}_s(T)), \qquad \Pr^{\max}_{s}(\mathit{reach}(T)) = \sup_{\sigma} \Pr^\sigma_{M,s}(\mathit{reach}_s(T)),$$

the infimum and supremum being taken over all adversaries. The *qualitative* sets are $S^0_{\min}$, $S^1_{\min}$, $S^0_{\max}$ and $S^1_{\max}$, the sets of states whose minimum, respectively maximum, reachability probability is $0$, respectively $1$.

## Depends on

- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 4 (introduction) and Section 4.1.
