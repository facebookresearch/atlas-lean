# Flow through an oriented edge

Let $F$ be a [multicommodity flow](multicommodity-flow.md) on a finite state space $S$, with path
sets $\mathcal{P}_{xy}$ and weights $w_{xy}(p) \ge 0$. The flow through the oriented edge $(u, v)$
is

$$f(u, v) = \sum_{x \ne y} \sum_{p \in \mathcal{P}_{xy}} w_{xy}(p)\, m_p(u, v),$$

where $m_p(u, v)$ is the number of times the path $p$ from $x$ uses $(u, v)$. The paths of a flow
are simple, so $m_p(u, v) \in \{0, 1\}$ and $f(u, v) = \sum_{p \ni (u, v)} w_{xy}(p)$, as in
Sinclair's Section 4.

## Sources

- A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*,
  Combinatorics, Probability and Computing 1 (1992), 351–370, Section 4.
