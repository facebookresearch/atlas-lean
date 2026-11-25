# Aldous tightness criterion in D([0,T],E) with initial and compact-containment conditions

Let $(E,r)$ be a Polish space, $T>0$, and for each $n$ let $X^n$ be a process with paths in the [Skorokhod space](skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md) $D([0,T],E)$, adapted to a filtration $(\mathcal F^n_t)$. Assume:

1. the laws of $X^n_0$ are tight;
2. compact containment: for every $\varepsilon>0$ there is a compact $K\subseteq E$ with $P(X^n_t\in K\text{ for all }t\le T)\ge1-\varepsilon$ for all $n$;
3. Aldous's condition: for all $(\mathcal F^n_t)$-stopping times $\tau_n$ with values in $[0,T]$ and all constants $\delta_n\to0$, $r\bigl(X^n_{(\tau_n+\delta_n)\wedge T},X^n_{\tau_n}\bigr)\to0$ in probability.

Then the laws of $X^n$ are tight in $D([0,T],E)$. If moreover $\sup_{t\le T}r(X^n_t,X^n_{t-})\to0$ in probability, every limit law is concentrated on $C([0,T],E)$.

Condition 2 implies condition 1. Neither can be dropped in favour of condition 3 alone: $X^n_t=n$ in $E=\mathbb R$ has zero increments and no jumps but is not tight. On a compact $E$ condition 2 is automatic, and for processes started at a fixed point (such as partial-sum processes started at $0$) condition 1 is automatic.

## Depends on

- [Skorokhod space D([0,T],E) for a metric space E: J1 topology and embeddings](skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md)

## Proof depends on

- [D([0,T],E) is Polish for Polish E](d-0-t-e-is-polish-for-polish-e.md)
- [Tightness in $D([0,T],E)$ from compact containment and the modulus $w'$](tightness-in-d-via-the-modulus-w-prime.md)
- [C-tightness: tight laws with vanishing maximal jumps have continuous limit points](c-tightness-criterion.md)

## Expansion

A proof page must establish tightness from conditions 1–3 through a modulus criterion for relative compactness in $D([0,T],E)$; fix from the sources the convention at the terminal time (here $\tau_n+\delta_n$ is truncated at $T$); prove the continuity of limits under vanishing maximal jumps; and record the guard example and the two automatic cases.

## Sources

- D. Aldous, *Stopping times and tightness*, Annals of Probability 6 (1978), 335–340, <https://statistics.berkeley.edu/people/david-aldous> (author page; Aldous criterion).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Chapter 3 (compact containment).
